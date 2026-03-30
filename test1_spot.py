import csv
import json
import math
import os
import threading
import time
from collections import deque
from datetime import datetime, timezone

import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.ticker import FormatStrFormatter
import websocket


# =========================
# CONFIG
# =========================
SYMBOL = "NOMUSDT"          # use a liquid spot symbol
MAX_POINTS = 600            # how many points to keep on chart
PRICE_DISPLAY_DECIMALS = 8
SNAPSHOT_INTERVAL_SECONDS = 0.1
EVENT_WINDOW_SECONDS = 3 * 60
PRE_EVENT_BUFFER_SNAPSHOTS = int(EVENT_WINDOW_SECONDS / SNAPSHOT_INTERVAL_SECONDS) + 20
CSV_OUTPUT_PATH = f"{SYMBOL.lower()}_spot_cross_under_events.csv"
WS_URL = (
    f"wss://stream.binance.com:9443/stream"
    f"?streams={SYMBOL.lower()}@depth5@100ms/{SYMBOL.lower()}@aggTrade"
)

# If you want to use Binance Spot's market-data-only endpoint instead, you can swap to:
# WS_URL = (
#     f"wss://data-stream.binance.vision:9443/stream"
#     f"?streams={SYMBOL.lower()}@depth5@100ms/{SYMBOL.lower()}@aggTrade"
# )

CSV_FIELDNAMES = [
    "event_id",
    "symbol",
    "event_time_utc",
    "snapshot_time_utc",
    "seconds_from_event",
    "window_side",
    "optimal_below_actual",
    "actual_price",
    "mid_price",
    "best_bid",
    "best_ask",
    "spread",
    "optimal_price",
    "microprice_3",
    "imbalance_3",
    "ob_vol_index",
    "bid_1_price",
    "bid_1_qty",
    "ask_1_price",
    "ask_1_qty",
    "bid_2_price",
    "bid_2_qty",
    "ask_2_price",
    "ask_2_qty",
    "bid_3_price",
    "bid_3_qty",
    "ask_3_price",
    "ask_3_qty",
]


# =========================
# SHARED STATE
# =========================
lock = threading.Lock()

times = deque(maxlen=MAX_POINTS)
actual_prices = deque(maxlen=MAX_POINTS)      # black line
optimal_prices = deque(maxlen=MAX_POINTS)     # red line
microprices = deque(maxlen=MAX_POINTS)
imbalances = deque(maxlen=MAX_POINTS)
ob_vol_indexes = deque(maxlen=MAX_POINTS)

last_trade_price = None
last_mid_price = None
prev_net_depth = None   # for OB volatility index
last_optimal_below_actual = None
next_event_id = 1
saved_event_count = 0
snapshot_history = deque(maxlen=PRE_EVENT_BUFFER_SNAPSHOTS)
active_event_windows = []


# =========================
# FORMULAS
# =========================
def safe_float(x):
    return float(x)


def compute_microprice_3levels(bids, asks):
    if len(bids) < 3 or len(asks) < 3:
        return None

    numer = 0.0
    denom = 0.0
    for level in range(3):
        bid_price = safe_float(bids[level][0])
        bid_qty = safe_float(bids[level][1])
        ask_price = safe_float(asks[level][0])
        ask_qty = safe_float(asks[level][1])

        numer += ask_price * bid_qty + bid_price * ask_qty
        denom += bid_qty + ask_qty

    if denom == 0:
        return None

    return numer / denom


def compute_imbalance_3levels(bids, asks):
    if len(bids) < 3 or len(asks) < 3:
        return None

    vb = safe_float(bids[0][1]) + safe_float(bids[1][1]) + safe_float(bids[2][1])
    va = safe_float(asks[0][1]) + safe_float(asks[1][1]) + safe_float(asks[2][1])

    denom = vb + va
    if denom == 0:
        return None

    return ((vb - va) / denom) / 100


def compute_ob_volatility_index_3levels(bids, asks, prev_net):
    if len(bids) < 3 or len(asks) < 3:
        return None, prev_net

    curr_ask = safe_float(asks[0][1]) + safe_float(asks[1][1]) + safe_float(asks[2][1])
    curr_bid = safe_float(bids[0][1]) + safe_float(bids[1][1]) + safe_float(bids[2][1])
    curr_net = curr_ask - curr_bid

    if prev_net is None or prev_net == 0:
        return float("nan"), curr_net

    ratio = curr_net / prev_net
    if ratio <= 0:
        return float("nan"), curr_net

    return math.log(ratio), curr_net


def compute_optimal_price(microprice, imbalance):
    if microprice is None or imbalance is None:
        return None
    return microprice * (1.0 + imbalance)


# =========================
# CSV EVENT CAPTURE
# =========================
def format_utc_timestamp(ts):
    return datetime.fromtimestamp(ts, tz=timezone.utc).isoformat(timespec="milliseconds")


def build_snapshot(ts, actual_price, mid_price, optimal_price, microprice, imbalance, ob_vol, bids, asks):
    best_bid = safe_float(bids[0][0])
    best_ask = safe_float(asks[0][0])
    return {
        "ts": ts,
        "actual_price": actual_price,
        "mid_price": mid_price,
        "best_bid": best_bid,
        "best_ask": best_ask,
        "spread": best_ask - best_bid,
        "optimal_price": optimal_price,
        "microprice_3": microprice,
        "imbalance_3": imbalance,
        "ob_vol_index": ob_vol,
        "optimal_below_actual": optimal_price < actual_price,
        "bid_1_price": safe_float(bids[0][0]),
        "bid_1_qty": safe_float(bids[0][1]),
        "ask_1_price": safe_float(asks[0][0]),
        "ask_1_qty": safe_float(asks[0][1]),
        "bid_2_price": safe_float(bids[1][0]),
        "bid_2_qty": safe_float(bids[1][1]),
        "ask_2_price": safe_float(asks[1][0]),
        "ask_2_qty": safe_float(asks[1][1]),
        "bid_3_price": safe_float(bids[2][0]),
        "bid_3_qty": safe_float(bids[2][1]),
        "ask_3_price": safe_float(asks[2][0]),
        "ask_3_qty": safe_float(asks[2][1]),
    }


def classify_window_side(snapshot_ts, event_ts):
    if abs(snapshot_ts - event_ts) < 1e-9:
        return "event"
    if snapshot_ts < event_ts:
        return "pre"
    return "post"


def create_event_window(snapshot):
    global next_event_id

    event_id = next_event_id
    next_event_id += 1

    window_start = snapshot["ts"] - EVENT_WINDOW_SECONDS
    rows = [dict(row) for row in snapshot_history if row["ts"] >= window_start]

    return {
        "event_id": event_id,
        "event_ts": snapshot["ts"],
        "end_ts": snapshot["ts"] + EVENT_WINDOW_SECONDS,
        "rows": rows,
        "last_snapshot_ts": rows[-1]["ts"] if rows else None,
    }


def snapshot_to_csv_row(event_window, snapshot):
    return {
        "event_id": event_window["event_id"],
        "symbol": SYMBOL,
        "event_time_utc": format_utc_timestamp(event_window["event_ts"]),
        "snapshot_time_utc": format_utc_timestamp(snapshot["ts"]),
        "seconds_from_event": round(snapshot["ts"] - event_window["event_ts"], 3),
        "window_side": classify_window_side(snapshot["ts"], event_window["event_ts"]),
        "optimal_below_actual": snapshot["optimal_below_actual"],
        "actual_price": snapshot["actual_price"],
        "mid_price": snapshot["mid_price"],
        "best_bid": snapshot["best_bid"],
        "best_ask": snapshot["best_ask"],
        "spread": snapshot["spread"],
        "optimal_price": snapshot["optimal_price"],
        "microprice_3": snapshot["microprice_3"],
        "imbalance_3": snapshot["imbalance_3"],
        "ob_vol_index": snapshot["ob_vol_index"],
        "bid_1_price": snapshot["bid_1_price"],
        "bid_1_qty": snapshot["bid_1_qty"],
        "ask_1_price": snapshot["ask_1_price"],
        "ask_1_qty": snapshot["ask_1_qty"],
        "bid_2_price": snapshot["bid_2_price"],
        "bid_2_qty": snapshot["bid_2_qty"],
        "ask_2_price": snapshot["ask_2_price"],
        "ask_2_qty": snapshot["ask_2_qty"],
        "bid_3_price": snapshot["bid_3_price"],
        "bid_3_qty": snapshot["bid_3_qty"],
        "ask_3_price": snapshot["ask_3_price"],
        "ask_3_qty": snapshot["ask_3_qty"],
    }


def append_event_window_to_csv(event_window):
    file_has_data = os.path.exists(CSV_OUTPUT_PATH) and os.path.getsize(CSV_OUTPUT_PATH) > 0

    with open(CSV_OUTPUT_PATH, "a", newline="", encoding="utf-8") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=CSV_FIELDNAMES)
        if not file_has_data:
            writer.writeheader()

        for snapshot in event_window["rows"]:
            writer.writerow(snapshot_to_csv_row(event_window, snapshot))


def update_event_windows(snapshot):
    global saved_event_count

    finished_events = []
    for event_window in active_event_windows:
        if snapshot["ts"] <= event_window["end_ts"]:
            if event_window["last_snapshot_ts"] != snapshot["ts"]:
                event_window["rows"].append(dict(snapshot))
                event_window["last_snapshot_ts"] = snapshot["ts"]
        else:
            finished_events.append(event_window)

    for event_window in finished_events:
        append_event_window_to_csv(event_window)
        active_event_windows.remove(event_window)
        saved_event_count += 1
        print(
            f"Saved event #{event_window['event_id']} with "
            f"{len(event_window['rows'])} snapshots to {CSV_OUTPUT_PATH}"
        )


# =========================
# WEBSOCKET HANDLERS
# =========================
def on_message(ws, message):
    global last_trade_price, last_mid_price, prev_net_depth, last_optimal_below_actual

    try:
        msg = json.loads(message)
        stream = msg.get("stream")
        data = msg.get("data", {})

        if stream is None:
            return

        if stream.endswith("@aggTrade") or data.get("e") == "aggTrade":
            last_trade_price = safe_float(data["p"])
            return

        if "@depth5@100ms" in stream or data.get("lastUpdateId") is not None:
            bids = data.get("bids") or data.get("b") or []
            asks = data.get("asks") or data.get("a") or []

            if len(bids) < 3 or len(asks) < 3:
                return

            best_bid = safe_float(bids[0][0])
            best_ask = safe_float(asks[0][0])
            last_mid_price = (best_bid + best_ask) / 2.0

            microprice = compute_microprice_3levels(bids, asks)
            imbalance = compute_imbalance_3levels(bids, asks)
            ob_vol, prev_net_depth = compute_ob_volatility_index_3levels(
                bids, asks, prev_net_depth
            )
            optimal_price = compute_optimal_price(microprice, imbalance)

            actual_price = last_trade_price if last_trade_price is not None else last_mid_price
            ts = time.time()

            if actual_price is None or optimal_price is None:
                return

            snapshot = build_snapshot(
                ts=ts,
                actual_price=actual_price,
                mid_price=last_mid_price,
                optimal_price=optimal_price,
                microprice=microprice,
                imbalance=imbalance,
                ob_vol=ob_vol,
                bids=bids,
                asks=asks,
            )

            with lock:
                times.append(ts)
                actual_prices.append(actual_price)
                optimal_prices.append(optimal_price)
                microprices.append(microprice)
                imbalances.append(imbalance)
                ob_vol_indexes.append(ob_vol)

                snapshot_history.append(dict(snapshot))

                current_below = snapshot["optimal_below_actual"]
                if last_optimal_below_actual is None:
                    last_optimal_below_actual = current_below
                elif (not last_optimal_below_actual) and current_below:
                    event_window = create_event_window(snapshot)
                    active_event_windows.append(event_window)
                    print(
                        f"Detected cross-under event #{event_window['event_id']} "
                        f"at {format_utc_timestamp(event_window['event_ts'])}"
                    )
                    last_optimal_below_actual = current_below
                else:
                    last_optimal_below_actual = current_below

                update_event_windows(snapshot)

    except Exception as e:
        print("on_message error:", e)


def on_error(ws, error):
    print("WebSocket error:", error)


def on_close(ws, close_status_code, close_msg):
    print("WebSocket closed:", close_status_code, close_msg)


def on_open(ws):
    print(f"Connected to Binance Spot stream for {SYMBOL}")


def run_ws():
    while True:
        try:
            ws = websocket.WebSocketApp(
                WS_URL,
                on_open=on_open,
                on_message=on_message,
                on_error=on_error,
                on_close=on_close,
            )
            ws.run_forever(ping_interval=20, ping_timeout=10)
        except Exception as e:
            print("Reconnect loop error:", e)

        print("Reconnecting in 3 seconds...")
        time.sleep(3)


# =========================
# LIVE CHART
# =========================
fig, (price_ax, imbalance_ax, obv_ax) = plt.subplots(
    3,
    1,
    figsize=(12, 10),
    sharex=True,
    gridspec_kw={"height_ratios": [2.2, 1, 1]},
)

price_line, = price_ax.plot([], [], label="Actual price", linewidth=1.6, color="black")
opt_line, = price_ax.plot([], [], label="Optimal price", linewidth=1.6, color="red")
micro_line, = price_ax.plot([], [], label="Microprice", linewidth=1.4, color="royalblue")

imbalance_line, = imbalance_ax.plot(
    [], [], label="Imbalance", linewidth=1.4, color="darkorange"
)
obv_line, = obv_ax.plot(
    [], [], label="OB volatility index", linewidth=1.4, color="seagreen"
)

imbalance_ax.axhline(0.0, color="gray", linewidth=0.9, linestyle="--", alpha=0.8)
obv_ax.axhline(0.0, color="gray", linewidth=0.9, linestyle="--", alpha=0.8)

info_text = price_ax.text(
    0.01, 0.98, "",
    transform=price_ax.transAxes,
    verticalalignment="top",
    fontsize=10,
    bbox=dict(boxstyle="round", facecolor="white", alpha=0.8)
)

price_ax.set_title(f"{SYMBOL} Binance Spot live price and indicators")
price_ax.set_ylabel("Price")
price_ax.legend(loc="upper right")

imbalance_ax.set_ylabel("Imbalance")
imbalance_ax.legend(loc="upper right")

obv_ax.set_xlabel("Seconds")
obv_ax.set_ylabel("OB vol")
obv_ax.legend(loc="upper right")
price_ax.yaxis.set_major_formatter(
    FormatStrFormatter(f"%.{PRICE_DISPLAY_DECIMALS}f")
)


def update_plot(frame):
    with lock:
        if len(times) < 2:
            return price_line, opt_line, micro_line, imbalance_line, obv_line, info_text

        x = list(times)
        y_price = list(actual_prices)
        y_opt = list(optimal_prices)
        y_micro = list(microprices)
        y_imbalance = list(imbalances)
        y_obv = list(ob_vol_indexes)

        x0 = x[0]
        x_rel = [t - x0 for t in x]

        price_line.set_data(x_rel, y_price)
        opt_line.set_data(x_rel, y_opt)
        micro_line.set_data(x_rel, y_micro)
        imbalance_line.set_data(x_rel, y_imbalance)
        obv_line.set_data(x_rel, y_obv)

        for axis in (price_ax, imbalance_ax, obv_ax):
            axis.relim()
            axis.autoscale_view()

        last_actual = actual_prices[-1] if len(actual_prices) else float("nan")
        last_opt = optimal_prices[-1] if len(optimal_prices) else float("nan")
        last_micro = microprices[-1] if len(microprices) else float("nan")
        last_imb = imbalances[-1] if len(imbalances) else float("nan")
        last_obv = ob_vol_indexes[-1] if len(ob_vol_indexes) else float("nan")

        info_text.set_text(
            f"{SYMBOL}\n"
            f"actual_price = {last_actual:.{PRICE_DISPLAY_DECIMALS}f}\n"
            f"optimal_price = {last_opt:.{PRICE_DISPLAY_DECIMALS}f}\n"
            f"microprice_3 = {last_micro:.{PRICE_DISPLAY_DECIMALS}f}\n"
            f"imbalance_3 = {last_imb:.6f}\n"
            f"OB vol index = {last_obv:.6f}\n"
            f"saved_events = {saved_event_count}\n"
            f"active_windows = {len(active_event_windows)}"
        )

    return price_line, opt_line, micro_line, imbalance_line, obv_line, info_text


def main():
    t = threading.Thread(target=run_ws, daemon=True)
    t.start()

    ani = FuncAnimation(fig, update_plot, interval=200, blit=False, cache_frame_data=False)
    plt.tight_layout()
    plt.show()


if __name__ == "__main__":
    main()
