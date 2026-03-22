"""
Modbus Coal Monitor
====================
Программа мониторинга данных угольных питателей в реальном времени.
Подключается к TMS320F28335 по RS-485/Modbus RTU.

Регистры 0-11:  расход угольной пыли питателей (ед. = 0.1 кг/ч)
Регистры 12-13: калорийность угля (ккал/кг)
Регистр  14:    управление (FC06 запись: 1=старт, 0=стоп)

Установка зависимостей:
    pip install pyserial matplotlib
"""

import tkinter as tk
from tkinter import ttk, messagebox, colorchooser
import serial
import serial.tools.list_ports
import struct
import threading
import time
import random
import collections
import sys
import os
import shutil
import subprocess
import urllib.request

import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

# ---------------------------------------------------------------------------
# Modbus RTU утилиты
# ---------------------------------------------------------------------------

def crc16_modbus(data: bytes) -> int:
    crc = 0xFFFF
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x0001:
                crc = (crc >> 1) ^ 0xA001
            else:
                crc >>= 1
    return crc


def build_fc03(slave_id: int, start_reg: int, count: int) -> bytes:
    pdu = struct.pack(">BBHH", slave_id, 0x03, start_reg, count)
    return pdu + struct.pack("<H", crc16_modbus(pdu))


def build_fc06(slave_id: int, reg: int, value: int) -> bytes:
    pdu = struct.pack(">BBHH", slave_id, 0x06, reg, value)
    return pdu + struct.pack("<H", crc16_modbus(pdu))


def parse_fc03(data: bytes, expected_count: int):
    expected_len = 5 + expected_count * 2
    if len(data) < expected_len:
        return None
    if data[1] & 0x80:
        return None
    if data[1] != 0x03:
        return None
    if data[2] not in (expected_count * 2, expected_count):
        return None
    if crc16_modbus(data[:-2]) != struct.unpack("<H", data[-2:])[0]:
        return None
    return [struct.unpack(">H", data[3 + i*2: 5 + i*2])[0]
            for i in range(expected_count)]


# ---------------------------------------------------------------------------
# Константы
# ---------------------------------------------------------------------------

SLAVE_ID         = 2
NUM_DATA_REGS    = 14
CTRL_REG         = 14
FREEZE_FLAGS_REG = 15   # регистр маски заморозки
FREEZE_VAL_REG   = 16   # первый регистр замороженных значений (16..27)
SOURCE_MODE_REG  = 64   # SourceMode[0..11] → регистры 64–75 (0=синусоида, 1=АЦП)
ADC_CHANNEL_REG  = 76   # AdcChannel[0..11] → регистры 76–87 (канал 0–15)
CAL_SOURCE_MODE_REG = 88  # CalSourceMode[0..1] → регистры 88–89 (0=симуляция, 1=АЦП)
CAL_ADC_CHANNEL_REG = 90  # CalAdcChannel[0..1] → регистры 90–91 (канал 0–15)
HISTORY_LEN   = 120
POLL_INTERVAL = 0.5

SIGNAL_NAMES = [f"Питатель {i+1}" for i in range(12)] + ["Калорийность 1", "Калорийность 2"]
SIGNAL_UNITS = ["кг/ч"] * 12 + ["ккал/кг"] * 2
SCALE        = [0.1] * 12 + [1.0] * 2
Y_MIN        = [0.0]  * 12 + [5000.0] * 2
Y_MAX        = [1100.0] * 12 + [7200.0] * 2
COLORS = [
    "#00bcd4", "#4caf50", "#ff9800", "#e91e63",
    "#9c27b0", "#03a9f4", "#ff5722", "#8bc34a",
    "#ffc107", "#3f51b5", "#009688", "#cddc39",
    "#f44336", "#ff8f00"
]

ALARM_HIGH = [850.0]  * 12 + [6700.0] * 2
ALARM_LOW  = [150.0]  * 12 + [5300.0] * 2

ALARM_NONE = 0
ALARM_HI   = 1
ALARM_LO   = 2

# Папка для логов
LOG_DIR = os.path.join(os.path.expanduser("~"), "Desktop", "LOGMODBUS")

# ---------------------------------------------------------------------------
# Версия и автообновление
# ---------------------------------------------------------------------------

VERSION = "1.0.1"

# ---------------------------------------------------------------------------
# Автообновление через интернет (GitHub)
#
# Как настроить:
#   1. Создайте репозиторий на https://github.com  (бесплатно)
#   2. Загрузите туда два файла: version.txt и monitor.py
#   3. Откройте version.txt на GitHub → нажмите "Raw" → скопируйте URL
#   4. Вставьте базовую часть URL в UPDATE_BASE_URL ниже
#
# Пример:
#   Ваш GitHub: https://github.com/ВашЛогин/ВашРепо
#   UPDATE_BASE_URL = "https://raw.githubusercontent.com/ВашЛогин/ВашРепо/main"
#
# Программа будет проверять:
#   UPDATE_BASE_URL/version.txt — номер доступной версии
#   UPDATE_BASE_URL/monitor.py  — новый скрипт для скачивания
#
# Оставьте пустым ("") чтобы ОТКЛЮЧИТЬ автообновление.
# ---------------------------------------------------------------------------
UPDATE_BASE_URL = "https://raw.githubusercontent.com/nt90380-design/coalmonitorr/refs/heads/main/CoalMonitor_GitHub"


def _parse_version(v: str):
    try:
        return tuple(int(x) for x in v.strip().split("."))
    except Exception:
        return (0,)


def _remote_version() -> str | None:
    """Проверяет version.txt на GitHub. Возвращает строку версии если доступно обновление."""
    if not UPDATE_BASE_URL:
        return None
    try:
        url = UPDATE_BASE_URL.rstrip("/") + "/version.txt"
        req = urllib.request.Request(url, headers={"Cache-Control": "no-cache"})
        with urllib.request.urlopen(req, timeout=10) as r:
            remote = r.read().decode("utf-8").strip()
        if _parse_version(remote) > _parse_version(VERSION):
            return remote
    except Exception:
        pass
    return None


# ---------------------------------------------------------------------------
# Демо-симуляция
# ---------------------------------------------------------------------------

class DemoSimulator:
    BASE_FLOW    = [500, 480, 520, 460, 540, 490, 510, 470, 530, 450, 500, 485]
    BASE_CALORIC = [5850, 6150]

    def __init__(self):
        self._vals   = [float(b) for b in self.BASE_FLOW + self.BASE_CALORIC]
        self._phase  = [random.uniform(0, 100) for _ in range(NUM_DATA_REGS)]
        self._spike_t  = [0] * NUM_DATA_REGS
        self._spike_tg = [0.0] * NUM_DATA_REGS
        self._t = 0

    def step(self) -> list:
        self._t += 1
        result = []
        for i in range(NUM_DATA_REGS):
            is_flow = i < 12
            base    = self.BASE_FLOW[i] if is_flow else self.BASE_CALORIC[i - 12]

            self._phase[i] += random.uniform(0.5, 2.5)
            drift = 60 * (0.5 - abs(((self._phase[i] % 100) / 100) - 0.5) * 2)
            noise = random.gauss(0, 12 if is_flow else 5)

            if self._spike_t[i] > 0:
                self._vals[i] += (self._spike_tg[i] - self._vals[i]) * 0.25
                self._spike_t[i] -= 1
            else:
                self._vals[i] += (base + drift - self._vals[i]) * 0.08 + noise
                if random.random() < 0.03:
                    anom = random.choice(["high", "low"])
                    dur  = random.randint(8, 25)
                    self._spike_t[i]  = dur
                    factor = (random.uniform(1.6, 2.2) if anom == "high"
                              else random.uniform(0.05, 0.25))
                    if not is_flow:
                        factor = 1.15 if anom == "high" else 0.87
                    self._spike_tg[i] = base * factor

            v = self._vals[i] + random.gauss(0, 3 if is_flow else 1.5)
            result.append(max(Y_MIN[i], min(Y_MAX[i], v)))
        return result


# ---------------------------------------------------------------------------
# Главное окно
# ---------------------------------------------------------------------------

class CoalMonitor:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Modbus Coal Monitor  v1.0.1")
        self.root.configure(bg="#1e1e1e")

        ico = os.path.join(os.path.dirname(os.path.abspath(__file__)), "coal_monitor.ico")
        if os.path.exists(ico):
            try:
                self.root.iconbitmap(ico)
            except Exception:
                pass
        self.root.geometry("1400x940")
        self.root.minsize(900, 660)

        self.port: serial.Serial | None = None
        self.running   = False
        self.demo_mode = False
        self.poll_thread: threading.Thread | None = None
        self.demo = DemoSimulator()

        self.history = [
            collections.deque([float(Y_MIN[i])] * HISTORY_LEN, maxlen=HISTORY_LEN)
            for i in range(NUM_DATA_REGS)
        ]
        self.x_data      = list(range(HISTORY_LEN))
        self.alarm_state = [ALARM_NONE] * NUM_DATA_REGS
        self.line_colors = list(COLORS)   # изменяемая копия цветов

        # Всплывающий полноэкранный график
        self._popup_win:    tk.Toplevel | None = None
        self._popup_idx:    int | None         = None
        self._popup_line:   plt.Line2D | None  = None
        self._popup_text:   plt.Text | None    = None
        self._popup_ax:     plt.Axes | None    = None
        self._popup_canvas: FigureCanvasTkAgg | None = None

        self._fail_count  = 0   # счётчик последовательных неудачных опросов
        self._freeze_mask = 0   # текущая маска заморозки (биты 0–11)
        self._freeze_vals = [0.0] * 12  # замороженные значения (кг/ч, для отображения)
        self._freeze_win: tk.Toplevel | None = None

        self._source_mode = [0] * 12          # 0=синусоида, 1=АЦП для каждого питателя
        self._adc_channel = list(range(12))   # номер АЦП-канала по умолчанию 0–11
        self._source_win: tk.Toplevel | None = None

        self._cal_source_mode = [0, 0]        # 0=симуляция, 1=АЦП для 2 каналов калорийности
        self._cal_adc_channel = [0, 1]        # АЦП-каналы для калорийности (по умолчанию 0 и 1)

        # Окно со всеми графиками
        self._all_win:    tk.Toplevel | None      = None
        self._all_lines:  list[plt.Line2D]         = []
        self._all_axes:   list[plt.Axes]           = []
        self._all_canvas: FigureCanvasTkAgg | None = None

        self._update_available: str | None = None
        self._update_btn: tk.Button | None = None

        self._ensure_log_dir()
        self._build_top_panel()
        self._build_value_bar()
        self._build_plots()
        self._build_alarm_log()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        if UPDATE_BASE_URL:
            threading.Thread(target=self._update_loop, daemon=True).start()

    # ------------------------------------------------------------------
    # Лог-файл
    # ------------------------------------------------------------------

    def _ensure_log_dir(self):
        os.makedirs(LOG_DIR, exist_ok=True)

    def _get_log_path(self) -> str:
        return os.path.join(LOG_DIR, f"log_{time.strftime('%Y-%m-%d')}.txt")

    def _write_log(self, ts: str, msg: str):
        try:
            with open(self._get_log_path(), "a", encoding="utf-8") as f:
                f.write(f"[{ts}] {msg}\n")
        except Exception:
            pass

    # ------------------------------------------------------------------
    # Построение интерфейса
    # ------------------------------------------------------------------

    def _build_top_panel(self):
        top = tk.Frame(self.root, bg="#2b2b2b", pady=6)
        top.pack(fill="x", padx=6, pady=(6, 0))

        tk.Label(top, text="COM порт:", bg="#2b2b2b", fg="#ccc",
                 font=("Arial", 9)).pack(side="left", padx=(8, 2))
        ports = [p.device for p in serial.tools.list_ports.comports()]
        self.com_var = tk.StringVar(value=ports[0] if ports else "COM3")
        self.com_combo = ttk.Combobox(top, textvariable=self.com_var,
                                      values=ports, width=8, state="readonly")
        self.com_combo.pack(side="left", padx=2)
        tk.Button(top, text="↺", bg="#2b2b2b", fg="#aaa", relief="flat",
                  command=self._refresh_ports, cursor="hand2").pack(side="left")

        tk.Label(top, text="Baud:", bg="#2b2b2b", fg="#ccc",
                 font=("Arial", 9)).pack(side="left", padx=(12, 2))
        self.baud_var = tk.StringVar(value="9600")
        tk.Entry(top, textvariable=self.baud_var, width=7,
                 bg="#333", fg="white", insertbackground="white").pack(side="left", padx=2)

        tk.Label(top, text="Интервал (с):", bg="#2b2b2b", fg="#ccc",
                 font=("Arial", 9)).pack(side="left", padx=(12, 2))
        self.interval_var = tk.StringVar(value=str(POLL_INTERVAL))
        tk.Entry(top, textvariable=self.interval_var, width=5,
                 bg="#333", fg="white", insertbackground="white").pack(side="left", padx=2)

        tk.Frame(top, bg="#2b2b2b", width=20).pack(side="left")

        self.connect_btn = tk.Button(
            top, text="⏻  Подключить", command=self._toggle_connect,
            bg="#4CAF50", fg="white", relief="flat", padx=10,
            font=("Arial", 9, "bold"), cursor="hand2")
        self.connect_btn.pack(side="left", padx=4)

        self.start_btn = tk.Button(
            top, text="▶  СТАРТ", command=self._start_polling,
            bg="#2196F3", fg="white", relief="flat", padx=10,
            font=("Arial", 9, "bold"), cursor="hand2", state="disabled")
        self.start_btn.pack(side="left", padx=4)

        self.stop_btn = tk.Button(
            top, text="■  СТОП", command=self._stop_polling,
            bg="#f44336", fg="white", relief="flat", padx=10,
            font=("Arial", 9, "bold"), cursor="hand2", state="disabled")
        self.stop_btn.pack(side="left", padx=4)

        self.demo_btn = tk.Button(
            top, text="◈  ДЕМО", command=self._toggle_demo,
            bg="#9c27b0", fg="white", relief="flat", padx=10,
            font=("Arial", 9, "bold"), cursor="hand2")
        self.demo_btn.pack(side="left", padx=4)

        tk.Button(top, text="🔒  Заморозка", command=self._open_freeze_dialog,
                  bg="#37474f", fg="#ccc", relief="flat", padx=10,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)

        tk.Button(top, text="📡  АЦП / Источник", command=self._open_source_dialog,
                  bg="#1a3a5c", fg="#64b5f6", relief="flat", padx=10,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)

        tk.Button(top, text="📊  Все графики", command=self._open_all_charts,
                  bg="#455a64", fg="white", relief="flat", padx=10,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)

        self.status_var = tk.StringVar(value="Не подключено")
        self.status_lbl = tk.Label(top, textvariable=self.status_var,
                                   bg="#2b2b2b", fg="#888",
                                   font=("Consolas", 9), anchor="e")
        self.status_lbl.pack(side="right", padx=12)

        # Кнопка обновления — скрыта до появления новой версии
        self._update_btn = tk.Button(
            top, text="", command=self._apply_update,
            bg="#e65100", fg="white", relief="flat", padx=12,
            font=("Arial", 9, "bold"), cursor="hand2")
        # .pack() будет вызван позже из _show_update_notify

    def _build_value_bar(self):
        bar = tk.Frame(self.root, bg="#252525", pady=4)
        bar.pack(fill="x", padx=6, pady=3)
        self.val_labels: list[tk.Label] = []
        self.val_cells:  list[tk.Frame] = []

        for i in range(NUM_DATA_REGS):
            cell = tk.Frame(bar, bg="#252525", relief="groove", bd=1)
            cell.grid(row=0, column=i, padx=2, sticky="ew")
            bar.columnconfigure(i, weight=1)
            name_lbl = tk.Label(cell, text=SIGNAL_NAMES[i], bg="#252525", fg="#888",
                                font=("Arial", 7), anchor="center")
            name_lbl.pack(fill="x")
            lbl = tk.Label(cell, text="---", bg="#252525", fg="#00e676",
                           font=("Consolas", 10, "bold"), anchor="center")
            lbl.pack(fill="x")
            lbl._name_lbl = name_lbl   # ссылка для обновления фона
            self.val_labels.append(lbl)
            self.val_cells.append(cell)

    def _build_plots(self):
        self.fig = plt.Figure(facecolor="#1a1a1a")
        self.fig.subplots_adjust(left=0.06, right=0.93, top=0.96, bottom=0.04)

        # Левая ось — расход питателей (кг/ч)
        self.ax_left = self.fig.add_subplot(111)
        # Правая ось — калорийность (ккал/кг)
        self.ax_right = self.ax_left.twinx()

        for a in (self.ax_left, self.ax_right):
            a.set_facecolor("#1a1a1a")
            a.tick_params(colors="#888", labelsize=9)
            for spine in a.spines.values():
                spine.set_color("#333")

        self.ax_left.set_ylim(-50, 1200)
        self.ax_right.set_ylim(4800, 7400)
        self.ax_left.set_xlim(0, HISTORY_LEN - 1)
        self.ax_left.xaxis.set_visible(False)
        self.ax_left.set_ylabel("кг/ч", color="#aaa", fontsize=10)
        self.ax_right.set_ylabel("ккал/кг", color="#ff9800", fontsize=10)
        self.ax_right.yaxis.label.set_color("#ff9800")
        self.ax_right.tick_params(axis="y", colors="#ff9800")

        # Линии порогов тревог
        self.ax_left.axhline(850, color="#ff4444", linewidth=0.8, linestyle="--", alpha=0.5)
        self.ax_left.axhline(150, color="#2196F3", linewidth=0.8, linestyle="--", alpha=0.5)
        self.ax_right.axhline(6700, color="#ff7722", linewidth=0.8, linestyle="--", alpha=0.5)
        self.ax_right.axhline(5300, color="#42a5f5", linewidth=0.8, linestyle="--", alpha=0.5)

        self.lines: list[plt.Line2D] = []
        self.axes:  list[plt.Axes]   = []

        for i in range(12):
            (line,) = self.ax_left.plot(
                self.x_data, list(self.history[i]),
                color=self.line_colors[i], linewidth=1.3,
                label=SIGNAL_NAMES[i], antialiased=True)
            self.lines.append(line)
            self.axes.append(self.ax_left)

        for i in range(12, NUM_DATA_REGS):
            (line,) = self.ax_right.plot(
                self.x_data, list(self.history[i]),
                color=self.line_colors[i], linewidth=2.0,
                linestyle="--", label=SIGNAL_NAMES[i], antialiased=True)
            self.lines.append(line)
            self.axes.append(self.ax_right)

        # Легенда — все 14 сигналов
        h1, l1 = self.ax_left.get_legend_handles_labels()
        h2, l2 = self.ax_right.get_legend_handles_labels()
        self.ax_left.legend(h1 + h2, l1 + l2,
                            loc="upper left", fontsize=8, ncol=4,
                            facecolor="#252525", edgecolor="#444",
                            labelcolor="#ccc", framealpha=0.85)

        canvas = FigureCanvasTkAgg(self.fig, master=self.root)
        canvas.get_tk_widget().pack(fill="both", expand=True, padx=6, pady=(0, 0))
        self.canvas = canvas

    def _build_alarm_log(self):
        frame = tk.Frame(self.root, bg="#1a1a1a", height=100)
        frame.pack(fill="x", padx=6, pady=(0, 6))
        frame.pack_propagate(False)

        header = tk.Frame(frame, bg="#1a1a1a")
        header.pack(fill="x")
        tk.Label(header, text="  ЖУРНАЛ ТРЕВОГ", bg="#1a1a1a", fg="#ff4444",
                 font=("Arial", 8, "bold")).pack(side="left")

        # Кнопка открыть папку с логами
        tk.Button(header, text="📁 Открыть папку логов", bg="#1a1a1a", fg="#888",
                  relief="flat", font=("Arial", 7), cursor="hand2",
                  command=lambda: os.startfile(LOG_DIR)).pack(side="right", padx=4)
        tk.Button(header, text="Очистить", bg="#1a1a1a", fg="#666",
                  relief="flat", font=("Arial", 7), cursor="hand2",
                  command=lambda: self.alarm_log.delete("1.0", "end")).pack(side="right")

        sb = tk.Scrollbar(frame, orient="vertical", bg="#1a1a1a")
        sb.pack(side="right", fill="y")
        self.alarm_log = tk.Text(
            frame, bg="#111", fg="#ccc", font=("Consolas", 8),
            height=5, state="disabled", wrap="word",
            yscrollcommand=sb.set, relief="flat", bd=0)
        self.alarm_log.pack(fill="both", expand=True)
        sb.config(command=self.alarm_log.yview)

        self.alarm_log.tag_config("high", foreground="#ff4444")
        self.alarm_log.tag_config("low",  foreground="#2196F3")
        self.alarm_log.tag_config("ok",   foreground="#4CAF50")
        self.alarm_log.tag_config("ts",   foreground="#555")

    # ------------------------------------------------------------------
    # Взаимодействие с графиками
    # ------------------------------------------------------------------

    def _on_canvas_click(self, event):
        """ЛКМ по графику → полноэкранный, ПКМ → выбор цвета."""
        if event.inaxes is None:
            return
        try:
            idx = self.axes.index(event.inaxes)
        except ValueError:
            return
        if event.button == 1:
            self._open_fullscreen(idx)
        elif event.button == 3:
            self._pick_color(idx)

    def _open_fullscreen(self, idx: int):
        """Открывает отдельное окно с увеличенным графиком сигнала."""
        # Закрыть предыдущий попап если открыт
        if self._popup_win and self._popup_win.winfo_exists():
            self._popup_win.destroy()

        win = tk.Toplevel(self.root)
        win.title(f"{SIGNAL_NAMES[idx]}  —  полный экран")
        win.configure(bg="#1a1a1a")
        win.geometry("1000x640")
        ico = os.path.join(os.path.dirname(os.path.abspath(__file__)), "coal_monitor.ico")
        if os.path.exists(ico):
            try:
                win.iconbitmap(ico)
            except Exception:
                pass

        fig = plt.Figure(facecolor="#1a1a1a")
        ax  = fig.add_subplot(111)
        ax.set_facecolor("#1a1a1a")
        ax.set_title(SIGNAL_NAMES[idx], color="#ccc", fontsize=16, pad=12)
        ax.set_ylim(Y_MIN[idx], Y_MAX[idx])
        ax.set_xlim(0, HISTORY_LEN - 1)
        ax.xaxis.set_visible(False)
        ax.tick_params(axis="y", colors="#888", labelsize=11)
        for spine in ax.spines.values():
            spine.set_color("#444")
        ax.set_ylabel(SIGNAL_UNITS[idx], fontsize=11, color="#888")
        ax.axhline(ALARM_HIGH[idx], color="#ff4444", linewidth=1.2,
                   linestyle="--", alpha=0.7, label=f"Макс {ALARM_HIGH[idx]:.0f}")
        ax.axhline(ALARM_LOW[idx],  color="#2196F3", linewidth=1.2,
                   linestyle="--", alpha=0.7, label=f"Мин  {ALARM_LOW[idx]:.0f}")
        ax.legend(loc="upper left", fontsize=9,
                  facecolor="#252525", edgecolor="#444", labelcolor="#ccc")

        color = self.line_colors[idx]
        (pop_line,) = ax.plot(self.x_data, list(self.history[idx]),
                              color=color, linewidth=2.2, antialiased=True)
        val_text = ax.text(0.98, 0.94, "---",
                           transform=ax.transAxes, ha="right", va="top",
                           color=color, fontsize=20, fontfamily="monospace")

        cv = FigureCanvasTkAgg(fig, master=win)
        cv.get_tk_widget().pack(fill="both", expand=True, padx=8, pady=8)
        cv.draw()

        self._popup_win    = win
        self._popup_idx    = idx
        self._popup_ax     = ax
        self._popup_line   = pop_line
        self._popup_text   = val_text
        self._popup_canvas = cv
        win.protocol("WM_DELETE_WINDOW", self._close_popup)

    def _close_popup(self):
        if self._popup_win:
            self._popup_win.destroy()
            self._popup_win = None

    def _open_all_charts(self):
        """Открывает большое окно со всеми 14 графиками в сетке 4×4."""
        if self._all_win and self._all_win.winfo_exists():
            self._all_win.lift()
            return

        win = tk.Toplevel(self.root)
        win.title("Все графики — Modbus Coal Monitor")
        win.configure(bg="#1a1a1a")
        win.state("zoomed")
        win.protocol("WM_DELETE_WINDOW", self._close_all_charts)
        self._all_win = win

        # 4 строки × 4 столбца: питатели 1-12 по 4 в ряд, калорийность в 4-й строке
        fig = plt.Figure(facecolor="#1a1a1a")
        gs = gridspec.GridSpec(4, 4, figure=fig,
                               hspace=0.55, wspace=0.3,
                               left=0.05, right=0.98,
                               top=0.97, bottom=0.04)

        # Позиции: 14 ячеек в порядке (row, col)
        positions = [(r, c) for r in range(4) for c in range(4)][:NUM_DATA_REGS]
        self._all_axes  = []
        self._all_lines = []

        for i, (r, c) in enumerate(positions):
            ax = fig.add_subplot(gs[r, c])
            ax.set_facecolor("#1a1a1a")
            ax.set_title(SIGNAL_NAMES[i], color="#ddd", fontsize=11, pad=4)
            ax.set_ylim(Y_MIN[i], Y_MAX[i])
            ax.set_xlim(0, HISTORY_LEN - 1)
            ax.xaxis.set_visible(False)
            ax.tick_params(axis="y", colors="#666", labelsize=8)
            for spine in ax.spines.values():
                spine.set_color("#333")
            ax.set_ylabel(SIGNAL_UNITS[i], fontsize=8, color="#666")
            ax.axhline(ALARM_HIGH[i], color="#ff4444", linewidth=0.8,
                       linestyle="--", alpha=0.6)
            ax.axhline(ALARM_LOW[i],  color="#2196F3", linewidth=0.8,
                       linestyle="--", alpha=0.6)

            (line,) = ax.plot(self.x_data, list(self.history[i]),
                              color=self.line_colors[i], linewidth=1.5, antialiased=True)
            txt = ax.text(0.98, 0.92, "---",
                          transform=ax.transAxes, ha="right", va="top",
                          color=self.line_colors[i], fontsize=11, fontfamily="monospace")
            line._val_text = txt

            # Текущее состояние тревоги
            alarm = self.alarm_state[i]
            if alarm == ALARM_HI:
                ax.set_facecolor("#261010")
                txt.set_color("#ff4444")
            elif alarm == ALARM_LO:
                ax.set_facecolor("#101828")
                txt.set_color("#42a5f5")

            self._all_axes.append(ax)
            self._all_lines.append(line)

        canvas = FigureCanvasTkAgg(fig, master=win)
        canvas.get_tk_widget().pack(fill="both", expand=True)
        self._all_canvas = canvas
        canvas.draw()

    def _close_all_charts(self):
        if self._all_win:
            self._all_win.destroy()
            self._all_win    = None
            self._all_lines  = []
            self._all_axes   = []
            self._all_canvas = None

    def _pick_color(self, idx: int):
        """Открывает диалог выбора цвета для линии графика."""
        result = colorchooser.askcolor(
            color=self.line_colors[idx],
            title=f"Цвет линии: {SIGNAL_NAMES[idx]}")
        if not result or not result[1]:
            return
        color = result[1]
        self.line_colors[idx] = color
        self.lines[idx].set_color(color)
        self.canvas.draw_idle()
        # Обновить цвет в попапе если открыт для этого сигнала
        if (self._popup_win and self._popup_win.winfo_exists()
                and self._popup_idx == idx):
            self._popup_line.set_color(color)
            if self.alarm_state[idx] == ALARM_NONE:
                self._popup_text.set_color(color)
            self._popup_canvas.draw_idle()

    # ------------------------------------------------------------------
    # Управление источником сигнала (Синусоида / АЦП)
    # ------------------------------------------------------------------

    def _open_source_dialog(self):
        if self._source_win and self._source_win.winfo_exists():
            self._source_win.lift()
            return

        win = tk.Toplevel(self.root)
        win.title("Источник сигнала питателей")
        win.configure(bg="#1e1e1e")
        win.geometry("530x660")
        win.resizable(False, True)
        win.transient(self.root)
        self._source_win = win
        ico = os.path.join(os.path.dirname(os.path.abspath(__file__)), "coal_monitor.ico")
        if os.path.exists(ico):
            try:
                win.iconbitmap(ico)
            except Exception:
                pass

        tk.Label(win, text="📡 Источник сигнала питателей", bg="#1e1e1e", fg="#64b5f6",
                 font=("Arial", 11, "bold")).pack(pady=(12, 2))
        tk.Label(win,
                 text="Синусоида — симуляция на контроллере   |   АЦП — реальный вход F28335",
                 bg="#1e1e1e", fg="#666", font=("Arial", 8)).pack(pady=(0, 6))

        # --- Таблица ---
        tbl = tk.Frame(win, bg="#2b2b2b", padx=10, pady=6)
        tbl.pack(fill="both", padx=12, pady=4, expand=True)

        for c, (h, w) in enumerate(
                zip(["Питатель", "Режим", "АЦП канал", ""], [16, 14, 10, 10])):
            tk.Label(tbl, text=h, bg="#2b2b2b", fg="#888",
                     font=("Arial", 8, "bold"), width=w).grid(
                row=0, column=c, padx=4, pady=(2, 4))

        mode_vars = []
        chan_vars  = []

        status_lbl = tk.Label(win, text="", bg="#1e1e1e", fg="#ffb74d",
                              font=("Arial", 8), wraplength=490)

        def _apply_row(i):
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            mode = 1 if mode_vars[i].get() == "АЦП" else 0
            try:
                ch = int(chan_vars[i].get())
                if not (0 <= ch <= 15):
                    raise ValueError
            except ValueError:
                status_lbl.config(
                    text=f"⚠ Питатель {i+1}: канал должен быть 0–15", fg="#f44336")
                return
            if mode == 1:
                self._send_fc06(ADC_CHANNEL_REG + i, ch)
            self._send_fc06(SOURCE_MODE_REG + i, mode)
            self._source_mode[i] = mode
            self._adc_channel[i] = ch
            self._mark_adc(i, mode == 1)
            label = f"АЦП кан. {ch} (ADCIN{'A' if ch < 8 else 'B'}{ch % 8})" if mode else "Синусоида"
            status_lbl.config(text=f"✓ Питатель {i+1} → {label}", fg="#4CAF50")

        for i in range(12):
            mode_val = "АЦП" if self._source_mode[i] == 1 else "Синусоида"
            mode_var = tk.StringVar(value=mode_val)
            chan_var  = tk.StringVar(value=str(self._adc_channel[i]))
            mode_vars.append(mode_var)
            chan_vars.append(chan_var)

            r = i + 1
            tk.Label(tbl, text=SIGNAL_NAMES[i], bg="#2b2b2b", fg="#ccc",
                     font=("Arial", 9), width=16, anchor="w").grid(
                row=r, column=0, padx=4, pady=2)

            mode_cb = ttk.Combobox(tbl, textvariable=mode_var,
                                   values=["Синусоида", "АЦП"], width=12, state="readonly")
            mode_cb.grid(row=r, column=1, padx=4, pady=2)

            tk.Spinbox(tbl, textvariable=chan_var, from_=0, to=15, width=8,
                       bg="#333", fg="white", buttonbackground="#444",
                       insertbackground="white", font=("Consolas", 9)).grid(
                row=r, column=2, padx=4, pady=2)

            tk.Button(tbl, text="Применить", width=9,
                      command=lambda i=i: _apply_row(i),
                      bg="#1565c0", fg="white", relief="flat",
                      font=("Arial", 8), cursor="hand2").grid(
                row=r, column=3, padx=4, pady=2)

        # --- Разделитель и секция калорийности ---
        tk.Frame(tbl, bg="#555", height=1).grid(
            row=13, column=0, columnspan=4, sticky="ew", padx=2, pady=(8, 2))
        tk.Label(tbl, text="  ▼  КАЛОРИЙНОСТЬ УГЛЯ", bg="#2b2b2b", fg="#ffb74d",
                 font=("Arial", 8, "bold")).grid(
            row=14, column=0, columnspan=4, sticky="w", padx=4, pady=(0, 4))

        cal_mode_vars = []
        cal_chan_vars  = []

        def _apply_cal_row(i):
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            mode = 1 if cal_mode_vars[i].get() == "АЦП" else 0
            try:
                ch = int(cal_chan_vars[i].get())
                if not (0 <= ch <= 15):
                    raise ValueError
            except ValueError:
                status_lbl.config(
                    text=f"⚠ Калорийность {i+1}: канал должен быть 0–15", fg="#f44336")
                return
            if mode == 1:
                self._send_fc06(CAL_ADC_CHANNEL_REG + i, ch)
            self._send_fc06(CAL_SOURCE_MODE_REG + i, mode)
            self._cal_source_mode[i] = mode
            self._cal_adc_channel[i] = ch
            self._mark_adc(12 + i, mode == 1)
            label = (f"АЦП кан. {ch} (ADCIN{'A' if ch < 8 else 'B'}{ch % 8})"
                     if mode else "Синусоида")
            status_lbl.config(text=f"✓ Калорийность {i+1} → {label}", fg="#4CAF50")

        for i in range(2):
            cal_mode_val = "АЦП" if self._cal_source_mode[i] == 1 else "Синусоида"
            cal_mode_var = tk.StringVar(value=cal_mode_val)
            cal_chan_var  = tk.StringVar(value=str(self._cal_adc_channel[i]))
            cal_mode_vars.append(cal_mode_var)
            cal_chan_vars.append(cal_chan_var)

            r = 15 + i
            tk.Label(tbl, text=SIGNAL_NAMES[12 + i], bg="#2b2b2b", fg="#ffb74d",
                     font=("Arial", 9), width=16, anchor="w").grid(
                row=r, column=0, padx=4, pady=2)
            mode_cb = ttk.Combobox(tbl, textvariable=cal_mode_var,
                                   values=["Синусоида", "АЦП"], width=12, state="readonly")
            mode_cb.grid(row=r, column=1, padx=4, pady=2)
            tk.Spinbox(tbl, textvariable=cal_chan_var, from_=0, to=15, width=8,
                       bg="#333", fg="white", buttonbackground="#444",
                       insertbackground="white", font=("Consolas", 9)).grid(
                row=r, column=2, padx=4, pady=2)
            tk.Button(tbl, text="Применить", width=9,
                      command=lambda i=i: _apply_cal_row(i),
                      bg="#e65100", fg="white", relief="flat",
                      font=("Arial", 8), cursor="hand2").grid(
                row=r, column=3, padx=4, pady=2)

        status_lbl.pack(fill="x", padx=12, pady=(4, 0))

        # --- Кнопки "применить всем" ---
        btn_frm = tk.Frame(win, bg="#1e1e1e")
        btn_frm.pack(pady=6)

        def _all_sinusoid():
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            for i in range(12):
                mode_vars[i].set("Синусоида")
                self._send_fc06(SOURCE_MODE_REG + i, 0)
                self._source_mode[i] = 0
                self._mark_adc(i, False)
            status_lbl.config(text="✓ Все питатели переведены на Синусоиду", fg="#4CAF50")

        def _all_adc():
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            for i in range(12):
                try:
                    ch = int(chan_vars[i].get())
                    if not (0 <= ch <= 15):
                        ch = self._adc_channel[i]
                except ValueError:
                    ch = self._adc_channel[i]
                mode_vars[i].set("АЦП")
                self._send_fc06(ADC_CHANNEL_REG + i, ch)
                self._send_fc06(SOURCE_MODE_REG + i, 1)
                self._source_mode[i] = 1
                self._adc_channel[i] = ch
                self._mark_adc(i, True)
            status_lbl.config(text="✓ Все питатели переведены на АЦП", fg="#4CAF50")

        def _all_cal_simulation():
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            for i in range(2):
                cal_mode_vars[i].set("Синусоида")
                self._send_fc06(CAL_SOURCE_MODE_REG + i, 0)
                self._cal_source_mode[i] = 0
                self._mark_adc(12 + i, False)
            status_lbl.config(text="✓ Оба канала калорийности → Синусоида", fg="#4CAF50")

        def _all_cal_adc():
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            for i in range(2):
                try:
                    ch = int(cal_chan_vars[i].get())
                    if not (0 <= ch <= 15):
                        ch = self._cal_adc_channel[i]
                except ValueError:
                    ch = self._cal_adc_channel[i]
                cal_mode_vars[i].set("АЦП")
                self._send_fc06(CAL_ADC_CHANNEL_REG + i, ch)
                self._send_fc06(CAL_SOURCE_MODE_REG + i, 1)
                self._cal_source_mode[i] = 1
                self._cal_adc_channel[i] = ch
                self._mark_adc(12 + i, True)
            status_lbl.config(text="✓ Оба канала калорийности → АЦП", fg="#4CAF50")

        row1 = tk.Frame(btn_frm, bg="#1e1e1e")
        row1.pack()
        tk.Label(row1, text="Питатели:", bg="#1e1e1e", fg="#aaa",
                 font=("Arial", 8)).pack(side="left", padx=(0, 4))
        tk.Button(row1, text="Синусоида — всем", command=_all_sinusoid,
                  bg="#00695c", fg="white", relief="flat", padx=10,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)
        tk.Button(row1, text="АЦП — всем", command=_all_adc,
                  bg="#4527a0", fg="white", relief="flat", padx=10,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)

        row2 = tk.Frame(btn_frm, bg="#1e1e1e")
        row2.pack(pady=(4, 0))
        tk.Label(row2, text="Калорийность:", bg="#1e1e1e", fg="#ffb74d",
                 font=("Arial", 8)).pack(side="left", padx=(0, 4))
        tk.Button(row2, text="Синусоида — обоим", command=_all_cal_simulation,
                  bg="#4e342e", fg="white", relief="flat", padx=10,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)
        tk.Button(row2, text="АЦП — обоим", command=_all_cal_adc,
                  bg="#311b92", fg="white", relief="flat", padx=10,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)

    # ------------------------------------------------------------------
    # Заморозка питателей
    # ------------------------------------------------------------------

    def _mark_frozen(self, idx: int, frozen: bool):
        """Визуальный маркер 🔒 на подписи питателя."""
        adc = (self._source_mode[idx] == 1)
        icons = ("🔒 " if frozen else "") + ("📡" if adc else "")
        self.val_labels[idx]._name_lbl.config(
            text=(icons + " " if icons else "") + SIGNAL_NAMES[idx])

    def _mark_adc(self, idx: int, adc: bool):
        """Визуальный маркер 📡 на подписи канала (АЦП-режим). idx 0–11: питатели, 12–13: калорийность."""
        frozen = bool(self._freeze_mask & (1 << idx)) if idx < 12 else False
        icons = ("🔒 " if frozen else "") + ("📡" if adc else "")
        self.val_labels[idx]._name_lbl.config(
            text=(icons + " " if icons else "") + SIGNAL_NAMES[idx])

    def _clear_all_frozen_ui(self):
        for i in range(12):
            if self._freeze_mask & (1 << i):
                self._mark_frozen(i, False)

    def _open_freeze_dialog(self):
        if self._freeze_win and self._freeze_win.winfo_exists():
            self._freeze_win.lift()
            return

        win = tk.Toplevel(self.root)
        win.title("Заморозка питателя")
        win.configure(bg="#1e1e1e")
        win.geometry("340x290")
        win.resizable(False, False)
        win.transient(self.root)
        self._freeze_win = win
        ico = os.path.join(os.path.dirname(os.path.abspath(__file__)), "coal_monitor.ico")
        if os.path.exists(ico):
            try:
                win.iconbitmap(ico)
            except Exception:
                pass

        tk.Label(win, text="🔒 Заморозка питателя", bg="#1e1e1e", fg="#64b5f6",
                 font=("Arial", 11, "bold")).pack(pady=(12, 4))

        frm = tk.Frame(win, bg="#2b2b2b", padx=14, pady=10)
        frm.pack(fill="x", padx=12, pady=4)

        tk.Label(frm, text="Питатель:", bg="#2b2b2b", fg="#ccc",
                 font=("Arial", 9)).grid(row=0, column=0, sticky="w", pady=4)
        feeder_var = tk.StringVar(value=SIGNAL_NAMES[0])
        feeder_combo = ttk.Combobox(frm, textvariable=feeder_var,
                                    values=SIGNAL_NAMES[:12], width=18, state="readonly")
        feeder_combo.grid(row=0, column=1, columnspan=2, sticky="w", padx=8, pady=4)

        tk.Label(frm, text="Текущее:", bg="#2b2b2b", fg="#ccc",
                 font=("Arial", 9)).grid(row=1, column=0, sticky="w", pady=4)
        cur_lbl = tk.Label(frm, text="---", bg="#2b2b2b", fg="#00e676",
                           font=("Consolas", 9))
        cur_lbl.grid(row=1, column=1, columnspan=2, sticky="w", padx=8)

        tk.Label(frm, text="Заморозить на:", bg="#2b2b2b", fg="#ccc",
                 font=("Arial", 9)).grid(row=2, column=0, sticky="w", pady=4)
        val_var = tk.StringVar()
        tk.Entry(frm, textvariable=val_var, width=10, bg="#333", fg="white",
                 insertbackground="white", font=("Consolas", 9)).grid(
            row=2, column=1, sticky="w", padx=8, pady=4)
        tk.Label(frm, text="кг/ч", bg="#2b2b2b", fg="#666",
                 font=("Arial", 8)).grid(row=2, column=2, sticky="w")

        status_lbl = tk.Label(win, text="", bg="#1e1e1e", fg="#ffb74d",
                               font=("Arial", 8), wraplength=300)
        status_lbl.pack(fill="x", padx=12, pady=(2, 0))

        frozen_lbl = tk.Label(win, text="", bg="#1e1e1e", fg="#64b5f6",
                               font=("Arial", 8), wraplength=300)
        frozen_lbl.pack(fill="x", padx=12)

        def _refresh_info(*_):
            idx = feeder_combo.current()
            if idx < 0:
                return
            if self._freeze_mask & (1 << idx):
                fval = self._freeze_vals[idx]
                cur_lbl.config(text=f"ЗАМОРОЖЕНО ({fval:.1f} кг/ч)", fg="#64b5f6")
                val_var.set(f"{fval:.1f}")
            else:
                if self.history[idx]:
                    cur = list(self.history[idx])[-1]
                    cur_lbl.config(text=f"{cur:.1f} кг/ч", fg="#00e676")
                    val_var.set(f"{cur:.1f}")
                else:
                    cur_lbl.config(text="---", fg="#888")
                    val_var.set("")
            frozen_names = [SIGNAL_NAMES[i] for i in range(12)
                            if self._freeze_mask & (1 << i)]
            frozen_lbl.config(text=("Заморожены: " + ", ".join(frozen_names))
                              if frozen_names else "Нет замороженных питателей")

        feeder_combo.bind("<<ComboboxSelected>>", _refresh_info)
        _refresh_info()

        btn_frm = tk.Frame(win, bg="#1e1e1e")
        btn_frm.pack(pady=10)

        def _freeze():
            idx = feeder_combo.current()
            if idx < 0:
                return
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            try:
                val = float(val_var.get())
            except ValueError:
                status_lbl.config(text="⚠ Введите числовое значение", fg="#f44336")
                return
            lo, hi = Y_MIN[idx], Y_MAX[idx]
            if not (lo <= val <= hi):
                status_lbl.config(text=f"⚠ Диапазон: {lo:.0f}–{hi:.0f} кг/ч", fg="#f44336")
                return
            raw = int(round(val / SCALE[idx]))
            self._send_fc06(FREEZE_VAL_REG + idx, raw)
            self._freeze_mask |= (1 << idx)
            self._send_fc06(FREEZE_FLAGS_REG, self._freeze_mask)
            self._freeze_vals[idx] = val
            self._mark_frozen(idx, True)
            status_lbl.config(text=f"✓ Питатель {idx+1} заморожен на {val:.1f} кг/ч",
                               fg="#4CAF50")
            _refresh_info()

        def _unfreeze():
            idx = feeder_combo.current()
            if idx < 0:
                return
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            self._freeze_mask &= ~(1 << idx)
            self._send_fc06(FREEZE_FLAGS_REG, self._freeze_mask)
            self._mark_frozen(idx, False)
            status_lbl.config(text=f"✓ Заморозка Питателя {idx+1} снята", fg="#4CAF50")
            _refresh_info()

        def _unfreeze_all():
            if not self.port or not self.port.is_open:
                status_lbl.config(text="⚠ Нет подключения к контроллеру", fg="#f44336")
                return
            self._clear_all_frozen_ui()
            self._freeze_mask = 0
            self._send_fc06(FREEZE_FLAGS_REG, 0)
            status_lbl.config(text="✓ Все заморозки сняты", fg="#4CAF50")
            _refresh_info()

        tk.Button(btn_frm, text="Заморозить", command=_freeze,
                  bg="#1565c0", fg="white", relief="flat", padx=12,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)
        tk.Button(btn_frm, text="Снять", command=_unfreeze,
                  bg="#e65100", fg="white", relief="flat", padx=12,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)
        tk.Button(btn_frm, text="Снять все", command=_unfreeze_all,
                  bg="#b71c1c", fg="white", relief="flat", padx=12,
                  font=("Arial", 9, "bold"), cursor="hand2").pack(side="left", padx=4)

    # ------------------------------------------------------------------
    # Управление портом
    # ------------------------------------------------------------------

    def _refresh_ports(self):
        ports = [p.device for p in serial.tools.list_ports.comports()]
        self.com_combo["values"] = ports
        if ports:
            self.com_var.set(ports[0])

    def _toggle_connect(self):
        if self.port and self.port.is_open:
            self._disconnect()
        else:
            self._connect()

    def _connect(self):
        try:
            baud = int(self.baud_var.get())
        except ValueError:
            messagebox.showerror("Ошибка", "Неверное значение baud rate")
            return
        try:
            self.port = serial.Serial(
                port=self.com_var.get(), baudrate=baud,
                bytesize=8, parity="N", stopbits=1, timeout=0.5)
            self.connect_btn.config(text="⏻  Отключить", bg="#f44336")
            self.start_btn.config(state="normal")
            self._set_status(f"Подключено: {self.com_var.get()} @ {baud}", "#4CAF50")
        except Exception as exc:
            messagebox.showerror("Ошибка порта", str(exc))

    def _disconnect(self):
        self._stop_polling()
        if self._freeze_mask and self.port and self.port.is_open:
            self._send_fc06(FREEZE_FLAGS_REG, 0)   # снять заморозку на контроллере
        self._clear_all_frozen_ui()
        self._freeze_mask = 0
        if self.port:
            try:
                self.port.close()
            except Exception:
                pass
            self.port = None
        self.connect_btn.config(text="⏻  Подключить", bg="#4CAF50")
        self.start_btn.config(state="disabled")
        self.stop_btn.config(state="disabled")
        self._set_status("Не подключено", "#888")

    # ------------------------------------------------------------------
    # Управление опросом / демо
    # ------------------------------------------------------------------

    def _toggle_demo(self):
        if self.running and self.demo_mode:
            self._stop_polling()
            self.demo_btn.config(text="◈  ДЕМО", bg="#9c27b0")
        else:
            if self.running:
                self._stop_polling()
            self.demo_mode = True
            self._set_status("ДЕМО-режим запущен", "#9c27b0")
            self._start_polling()
            self.demo_btn.config(text="■  СТОП ДЕМО", bg="#7b1fa2")

    def _start_polling(self):
        if self.running:
            return
        if not self.demo_mode and not self.port:
            return
        if not self.demo_mode:
            self._send_fc06(CTRL_REG, 1)
        self.running = True
        self.start_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        mode = "ДЕМО" if self.demo_mode else "Опрос"
        self._set_status(f"{mode} запущен…", "#2196F3")
        self.poll_thread = threading.Thread(target=self._poll_loop, daemon=True)
        self.poll_thread.start()

    def _stop_polling(self):
        if not self.running:
            return
        self.running   = False
        self.demo_mode = False
        if self.port and self.port.is_open:
            self._send_fc06(CTRL_REG, 0)
        self.start_btn.config(state="normal" if self.port else "disabled")
        self.stop_btn.config(state="disabled")
        self.demo_btn.config(text="◈  ДЕМО", bg="#9c27b0")
        self._set_status("Остановлено", "#ff9800")

    def _send_fc06(self, reg: int, value: int):
        if not self.port or not self.port.is_open:
            return
        try:
            cmd = build_fc06(SLAVE_ID, reg, value)
            self.port.reset_input_buffer()
            self.port.write(cmd)
            time.sleep(0.15)
            self.port.read(8)
        except Exception:
            pass

    # ------------------------------------------------------------------
    # Поток опроса
    # ------------------------------------------------------------------

    def _poll_loop(self):
        req      = build_fc03(SLAVE_ID, 0, NUM_DATA_REGS)
        expected = 5 + NUM_DATA_REGS * 2

        while self.running:
            t_start = time.time()

            if self.demo_mode:
                real_vals = self.demo.step()
                self.root.after(0, self._update_ui, real_vals)
            else:
                try:
                    self.port.reset_input_buffer()
                    self.port.write(req)
                    resp   = self.port.read(expected)
                    values = parse_fc03(resp, NUM_DATA_REGS)
                    if values:
                        self._fail_count = 0
                        real_vals = [values[i] * SCALE[i] for i in range(NUM_DATA_REGS)]
                        self.root.after(0, self._update_ui, real_vals)
                    elif self.running and not self.demo_mode:
                        self._fail_count += 1
                        if self._fail_count >= 3:
                            self.root.after(0, self._set_status,
                                           f"Нет ответа / ошибка CRC ({len(resp)} байт)",
                                           "#ff9800")
                except serial.SerialException as exc:
                    if self.running and not self.demo_mode:
                        self.root.after(0, self._set_status,
                                       f"Ошибка порта: {exc}", "#f44336")
                    self.running = False
                    break

            try:
                interval = float(self.interval_var.get())
            except ValueError:
                interval = POLL_INTERVAL
            time.sleep(max(0.05, interval - (time.time() - t_start)))

    # ------------------------------------------------------------------
    # Обновление UI + тревоги
    # ------------------------------------------------------------------

    def _update_ui(self, real_vals: list):
        for i, real in enumerate(real_vals):
            self.history[i].append(real)
            text = f"{real:.1f}" if i < 12 else f"{real:.0f}"

            # Детект тревоги
            prev_state = self.alarm_state[i]
            if real > ALARM_HIGH[i]:
                new_state = ALARM_HI
            elif real < ALARM_LOW[i]:
                new_state = ALARM_LO
            else:
                new_state = ALARM_NONE

            if new_state != prev_state:
                self.alarm_state[i] = new_state
                self._on_alarm_change(i, new_state, real)

            # Цвет панели значений
            if new_state == ALARM_HI:
                fg_c, bg_c = "#ff4444", "#3a1a1a"
            elif new_state == ALARM_LO:
                fg_c, bg_c = "#42a5f5", "#1a2a3a"
            else:
                fg_c, bg_c = "#00e676", "#252525"

            self.val_labels[i].config(text=text, fg=fg_c, bg=bg_c)
            self.val_labels[i]._name_lbl.config(bg=bg_c)
            self.val_cells[i].config(bg=bg_c)

            # Линия на графике
            self.lines[i].set_ydata(list(self.history[i]))
            # Тревога — подсветить линию толщиной
            if new_state != ALARM_NONE:
                self.lines[i].set_linewidth(2.5)
            else:
                self.lines[i].set_linewidth(2.0 if i >= 12 else 1.3)

        self.canvas.draw_idle()

        # Обновить полноэкранный попап
        if (self._popup_win and self._popup_win.winfo_exists()
                and self._popup_idx is not None):
            pi   = self._popup_idx
            real = real_vals[pi]
            self._popup_line.set_ydata(list(self.history[pi]))
            text = f"{real:.1f}" if pi < 12 else f"{real:.0f}"
            self._popup_text.set_text(f"{text} {SIGNAL_UNITS[pi]}")
            alarm = self.alarm_state[pi]
            if alarm == ALARM_HI:
                self._popup_ax.set_facecolor("#261010")
                self._popup_text.set_color("#ff4444")
            elif alarm == ALARM_LO:
                self._popup_ax.set_facecolor("#101828")
                self._popup_text.set_color("#42a5f5")
            else:
                self._popup_ax.set_facecolor("#1a1a1a")
                self._popup_text.set_color(self.line_colors[pi])
            self._popup_canvas.draw_idle()

        # Обновить окно со всеми графиками
        if self._all_win and self._all_win.winfo_exists():
            for i in range(NUM_DATA_REGS):
                real = real_vals[i]
                self._all_lines[i].set_ydata(list(self.history[i]))
                text = f"{real:.1f}" if i < 12 else f"{real:.0f}"
                self._all_lines[i]._val_text.set_text(f"{text} {SIGNAL_UNITS[i]}")
                alarm = self.alarm_state[i]
                if alarm == ALARM_HI:
                    self._all_axes[i].set_facecolor("#261010")
                    self._all_lines[i]._val_text.set_color("#ff4444")
                elif alarm == ALARM_LO:
                    self._all_axes[i].set_facecolor("#101828")
                    self._all_lines[i]._val_text.set_color("#42a5f5")
                else:
                    self._all_axes[i].set_facecolor("#1a1a1a")
                    self._all_lines[i]._val_text.set_color(self.line_colors[i])
            self._all_canvas.draw_idle()

        # Статусная строка
        alarms_active = sum(1 for s in self.alarm_state if s != ALARM_NONE)
        mode = "ДЕМО" if self.demo_mode else time.strftime("%H:%M:%S")
        if alarms_active:
            self._set_status(f"⚠  ТРЕВОГА: {alarms_active} сигн.  |  {mode}", "#ff4444")
        else:
            self._set_status(f"Обновлено: {mode}  | {NUM_DATA_REGS} рег.", "#4CAF50")

    def _on_alarm_change(self, i: int, new: int, value: float):
        ts   = time.strftime("%H:%M:%S")
        name = SIGNAL_NAMES[i]
        unit = SIGNAL_UNITS[i]
        fmt  = f"{value:.1f}" if i < 12 else f"{value:.0f}"

        if new == ALARM_HI:
            msg = f"▲ ПРЕВЫШЕНИЕ — {name}: {fmt} {unit}  (порог >{ALARM_HIGH[i]:.0f})"
            tag = "high"
        elif new == ALARM_LO:
            msg = f"▼ НЕДОСТАТОК — {name}: {fmt} {unit}  (порог <{ALARM_LOW[i]:.0f})"
            tag = "low"
        else:
            msg = f"✓ Восстановлено — {name}: {fmt} {unit}"
            tag = "ok"

        # UI-лог
        self.alarm_log.config(state="normal")
        self.alarm_log.insert("end", f"[{ts}] ", "ts")
        self.alarm_log.insert("end", msg + "\n", tag)
        self.alarm_log.see("end")
        self.alarm_log.config(state="disabled")

        # Файловый лог
        self._write_log(ts, msg)

        if new != ALARM_NONE:
            self.root.bell()

    def _set_status(self, text: str, color: str = "#888"):
        self.status_var.set(text)
        self.status_lbl.config(fg=color)

    # ------------------------------------------------------------------
    # Автообновление
    # ------------------------------------------------------------------

    def _update_loop(self):
        """Фоновый поток: ждёт интернета и проверяет обновления каждый час."""
        time.sleep(15)  # небольшая задержка при старте
        while True:
            ver = _remote_version()
            if ver:
                self._update_available = ver
                self.root.after(0, self._show_update_notify)
                break
            # Если нет интернета или версия не новее — повторить через час
            time.sleep(3600)

    def _show_update_notify(self):
        """Показывает кнопку обновления в верхней панели."""
        if self._update_btn is None:
            return
        self._update_btn.config(
            text=f"🔔  Доступно обновление v{self._update_available}  — нажмите для установки")
        self._update_btn.pack(side="right", padx=8, before=self.status_lbl)
        # Мигание кнопки для привлечения внимания
        self._blink_update_btn(True)

    def _blink_update_btn(self, state: bool):
        if self._update_btn is None or self._update_available is None:
            return
        self._update_btn.config(bg="#e65100" if state else "#bf360c")
        self.root.after(700, self._blink_update_btn, not state)

    def _apply_update(self):
        """Скачивает новый monitor.py с GitHub и перезапускает программу."""
        if not self._update_available or not UPDATE_BASE_URL:
            return
        if not messagebox.askyesno(
            "Обновление CoalMonitor",
            f"Доступна версия {self._update_available}.\n\n"
            "Скачать и установить обновление?\n"
            "Программа автоматически перезапустится."
        ):
            return
        try:
            url = UPDATE_BASE_URL.rstrip("/") + "/monitor.py"
            dst = os.path.abspath(__file__)
            # Скачиваем во временный файл, потом заменяем
            tmp = dst + ".update"
            urllib.request.urlretrieve(url, tmp)
            shutil.move(tmp, dst)
            subprocess.Popen([sys.executable, dst])
            self.root.after(300, sys.exit)
        except Exception as e:
            messagebox.showerror("Ошибка обновления",
                                 f"Не удалось скачать обновление:\n{e}")

    def _on_close(self):
        self._close_popup()
        self._close_all_charts()
        self._disconnect()
        self.root.destroy()


# ---------------------------------------------------------------------------
# Точка входа
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    root = tk.Tk()
    try:
        app = CoalMonitor(root)
        root.mainloop()
    except KeyboardInterrupt:
        root.destroy()
        sys.exit(0)
