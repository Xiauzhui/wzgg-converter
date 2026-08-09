#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
简化字转换程序（单文件版 v5.2）

目录结构：
    wzgg_converter_v5_2.py
    code/
        1977.wzgg
        1977A.wzgg
    待转换文件.txt

运行：
    python wzgg_converter_v5_2.py

功能：
1. 扫描 code 目录中名称为“4位年份 + 可选1位大写字母”的 .wzgg 字表。
2. 多个字表时，用 ↑ ↓ 选择；只有一个时直接采用。
3. 解析四种规则：
       A［BC］、A〔BC〕：B、C 分别转换为 A。
       目标词〖来源词1〗〖来源词2〗……：多个异形词都转换为同一目标词，
       整词转换时按来源词最长优先。
       A〈BC〉：整条规则忽略。
4. 字表标准化：
       同目标规则自动合并；同一来源字对应多个目标字时，用 ← → 选择；
       连续简化关系递归压缩到最终目标，例如 a［b］、c［a］ → c［ab］。
       三类处理可交错反复执行，直到稳定；循环关系会明确报错。
       标准化结果写回原字表。
5. 先做词语转换，再做单字转换。
6. 扫描程序目录下全部 .txt，输出“原名（字表名）.wzgg”。
7. 字表含“=叠字符=”时，全部常规转换完成后处理连续叠字；私用区字符也按汉字处理。

仅使用 Python 标准库；Python 字符串按 Unicode 码点处理，支持补充平面字符。
"""

from __future__ import annotations

import os
import re
import select
import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional


# ============================================================
# 基本配置
# ============================================================

PROGRAM_VERSION = "5.2.0"
BASE_DIR = Path(__file__).resolve().parent
CODE_DIR = BASE_DIR / "code"
ERROR_REPORT_PATH = BASE_DIR / "字表错误报告.txt"
REPEAT_DIRECTIVE = "=叠字符="
REPEAT_MARK = "𠚤"
SCHEME_NAME_RE = re.compile(r"^(\d{4})([A-Z]?)\.(?i:wzgg)$")

OPEN_TO_CLOSE = {
    "［": "］",
    "〔": "〕",
    "〖": "〗",
    "〈": "〉",
}
ALL_OPEN = set(OPEN_TO_CLOSE)
ALL_CLOSE = set(OPEN_TO_CLOSE.values())
ALL_BRACKETS = ALL_OPEN | ALL_CLOSE


# ============================================================
# 数据结构
# ============================================================

@dataclass
class Rule:
    kind: str          # "char"、"word"、"ignore"
    dst: str           # 括号外、左侧内容；连续词语括号会继承同一 dst
    src: str           # 括号内内容
    opener: str        # 原始左括号
    write_dst: bool = True  # 回写时是否在本括号前写出 dst

    @property
    def closer(self) -> str:
        return OPEN_TO_CLOSE[self.opener]

    def serialize(self) -> str:
        prefix = self.dst if self.write_dst else ""
        return f"{prefix}{self.opener}{self.src}{self.closer}"


@dataclass
class Scheme:
    path: Path
    rules: list[Rule]
    repeat_enabled: bool = False

    @property
    def char_rules(self) -> list[Rule]:
        return [rule for rule in self.rules if rule.kind == "char"]

    @property
    def word_rules(self) -> list[Rule]:
        return [rule for rule in self.rules if rule.kind == "word"]


class UserCancelled(Exception):
    """用户按 Esc 退出。"""


@dataclass(frozen=True)
class SourceLocation:
    """去除换行前，某个有效字符在原字表中的位置。"""

    line: int
    column: int


class SchemeParseError(ValueError):
    """带原文件行列号和上下文片段的字表解析错误。"""

    def __init__(
        self,
        path: Path,
        message: str,
        flat_text: str,
        flat_index: int,
        locations: list[SourceLocation],
        end_location: SourceLocation,
    ) -> None:
        super().__init__(message)
        self.path = path
        self.message = message
        self.flat_text = flat_text
        self.flat_index = max(0, min(flat_index, len(flat_text)))
        self.locations = locations
        self.end_location = end_location

    @staticmethod
    def _visible(text: str) -> str:
        """把容易看不见的空白显示出来，普通字符保持原样。"""
        result: list[str] = []
        for ch in text:
            if ch == " ":
                result.append("␠")
            elif ch == "\t":
                result.append("⇥")
            elif ord(ch) < 32 or ord(ch) == 127:
                result.append(f"\\u{ord(ch):04X}")
            else:
                result.append(ch)
        return "".join(result)

    def __str__(self) -> str:
        index = self.flat_index
        if index < len(self.locations):
            location = self.locations[index]
            ordinal = index + 1
            current = self.flat_text[index]
            current_description = f"{current!r}（{codepoint_label(current)}）"
        else:
            location = self.end_location
            ordinal = len(self.flat_text) + 1
            current = ""
            current_description = "文件末尾"

        radius = 36
        start = max(0, index - radius)
        end = min(len(self.flat_text), index + 1 + radius)
        before = self._visible(self.flat_text[start:index])
        marked = self._visible(current) if current else "文件末尾"
        after_start = index + 1 if current else index
        after = self._visible(self.flat_text[after_start:end])
        left_ellipsis = "…" if start > 0 else ""
        right_ellipsis = "…" if end < len(self.flat_text) else ""

        context = (
            f"{left_ellipsis}{before} >>>{marked}<<< {after}{right_ellipsis}"
        )
        return (
            f"{self.path.name}：{self.message}\n"
            f"位置：原文件第 {location.line} 行、第 {location.column} 列；"
            f"去除换行后的第 {ordinal} 个字符。\n"
            f"当前：{current_description}\n"
            f"上下文：{context}"
        )


def flatten_scheme_text(
    raw_text: str,
) -> tuple[str, list[SourceLocation], SourceLocation]:
    """
    删除 CR、LF、CRLF，并忽略“=叠字符=”指令，同时记录每个保留字符
    在原文件中的行列位置。这样指令不会参与任何规则解析，但其后的
    报错位置仍然对应原字表。
    """
    flat_chars: list[str] = []
    locations: list[SourceLocation] = []
    line = 1
    column = 1
    i = 0

    while i < len(raw_text):
        if raw_text.startswith(REPEAT_DIRECTIVE, i):
            i += len(REPEAT_DIRECTIVE)
            column += len(REPEAT_DIRECTIVE)
            continue

        ch = raw_text[i]
        if ch == "\r":
            if i + 1 < len(raw_text) and raw_text[i + 1] == "\n":
                i += 2
            else:
                i += 1
            line += 1
            column = 1
            continue
        if ch == "\n":
            i += 1
            line += 1
            column = 1
            continue

        flat_chars.append(ch)
        locations.append(SourceLocation(line, column))
        i += 1
        column += 1

    return "".join(flat_chars), locations, SourceLocation(line, column)


# ============================================================
# 控制台键盘与菜单
# ============================================================

def clear_screen() -> None:
    """清空控制台。"""
    if os.name == "nt":
        os.system("cls")
    else:
        print("\033[2J\033[H", end="", flush=True)


def read_key() -> str:
    """
    读取一个控制键，返回：up/down/left/right/enter/esc/other。
    Windows 使用 msvcrt；类 Unix 使用 termios。
    """
    if not sys.stdin.isatty():
        return "other"

    if os.name == "nt":
        import msvcrt

        ch = msvcrt.getwch()
        if ch in ("\x00", "\xe0"):
            code = msvcrt.getwch()
            return {
                "H": "up",
                "P": "down",
                "K": "left",
                "M": "right",
            }.get(code, "other")
        if ch == "\r":
            return "enter"
        if ch == "\x1b":
            return "esc"
        return "other"

    import termios
    import tty

    fd = sys.stdin.fileno()
    old_settings = termios.tcgetattr(fd)
    try:
        tty.setraw(fd)
        ch = sys.stdin.read(1)
        if ch in ("\r", "\n"):
            return "enter"
        if ch != "\x1b":
            return "other"

        # 单独的 Esc 与方向键均以 ESC 开头；短暂检查后续字节。
        ready, _, _ = select.select([sys.stdin], [], [], 0.06)
        if not ready:
            return "esc"

        second = sys.stdin.read(1)
        if second != "[":
            return "esc"

        ready, _, _ = select.select([sys.stdin], [], [], 0.06)
        if not ready:
            return "esc"

        third = sys.stdin.read(1)
        return {
            "A": "up",
            "B": "down",
            "C": "right",
            "D": "left",
        }.get(third, "other")
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)


def choose_vertical(title: str, options: list[str]) -> int:
    """用 ↑ ↓ 选择一项，返回下标。"""
    if not options:
        raise ValueError("菜单没有可选项。")
    if len(options) == 1:
        return 0

    if not sys.stdin.isatty():
        print(title)
        for i, option in enumerate(options, start=1):
            print(f"  {i}. {option}")
        while True:
            raw = input("请输入序号：").strip()
            if raw.isdigit() and 1 <= int(raw) <= len(options):
                return int(raw) - 1

    selected = 0
    while True:
        clear_screen()
        print(title)
        print("使用 ↑ ↓ 选择，Enter 确认，Esc 退出。\n")
        for i, option in enumerate(options):
            marker = ">" if i == selected else " "
            print(f"{marker} {option}")

        key = read_key()
        if key == "up":
            selected = (selected - 1) % len(options)
        elif key == "down":
            selected = (selected + 1) % len(options)
        elif key == "enter":
            return selected
        elif key == "esc":
            raise UserCancelled


def codepoint_label(text: str) -> str:
    """给一个字符生成 U+XXXX 标签。"""
    return " ".join(f"U+{ord(ch):04X}" for ch in text)


def choose_horizontal(source_char: str, candidates: list[str]) -> str:
    """用 ← → 在冲突目标中选择一个。"""
    if not candidates:
        raise ValueError("冲突没有候选目标。")
    if len(candidates) == 1:
        return candidates[0]

    if not sys.stdin.isatty():
        print(f"\n来源字符 {source_char!r}（{codepoint_label(source_char)}）存在冲突：")
        for i, candidate in enumerate(candidates, start=1):
            print(f"  {i}. {candidate}")
        while True:
            raw = input("请输入要保留的序号：").strip()
            if raw.isdigit() and 1 <= int(raw) <= len(candidates):
                return candidates[int(raw) - 1]

    selected = 0
    while True:
        clear_screen()
        print("发现一繁对多简冲突")
        print(f"来源字符：{source_char}（{codepoint_label(source_char)}）")
        print("使用 ← → 选择，Enter 确认，Esc 退出。\n")

        rendered: list[str] = []
        for i, candidate in enumerate(candidates):
            if i == selected:
                rendered.append(f"[ {candidate} ]")
            else:
                rendered.append(f"  {candidate}  ")
        print("   ".join(rendered))

        key = read_key()
        if key == "left":
            selected = (selected - 1) % len(candidates)
        elif key == "right":
            selected = (selected + 1) % len(candidates)
        elif key == "enter":
            return candidates[selected]
        elif key == "esc":
            raise UserCancelled


# ============================================================
# 字表扫描与解析
# ============================================================

def scheme_sort_key(path: Path) -> tuple[int, int, str]:
    match = SCHEME_NAME_RE.fullmatch(path.name)
    if match is None:
        return (9999, 1, path.name)
    year = int(match.group(1))
    suffix = match.group(2).upper()
    # 无后缀排在 A、B……之前。
    return (year, 0 if suffix == "" else 1, suffix)


def find_scheme_files() -> list[Path]:
    if not CODE_DIR.exists():
        CODE_DIR.mkdir(parents=True, exist_ok=True)
        return []

    files = [
        path
        for path in CODE_DIR.iterdir()
        if path.is_file() and SCHEME_NAME_RE.fullmatch(path.name)
    ]
    return sorted(files, key=scheme_sort_key)


def parse_scheme(path: Path) -> Scheme:
    """
    解析字表。

    换行符被删除。每条规则通常由“左侧内容 + 一对全角括号”组成。
    字规则和忽略规则的左侧必须正好是一个 Unicode 码点。
    词语规则的左侧可以是任意非空长度，并允许连续书写多个 〖〗：

        ab〖tr〗〖RF〗〖yu〗

    上例会解析成三条来源词规则：tr、RF、yu 都转换为 ab。
    只有紧接在词语规则后的 〖〗 才允许省略左侧内容。
    """
    try:
        raw_text = path.read_text(encoding="utf-8-sig")
    except UnicodeDecodeError as exc:
        raise ValueError(
            f"{path.name} 不是有效的 UTF-8 文件；无法解析的字节位置约为 {exc.start}。"
        ) from exc

    repeat_enabled = REPEAT_DIRECTIVE in raw_text
    text, locations, end_location = flatten_scheme_text(raw_text)
    rules: list[Rule] = []
    pos = 0
    rule_number = 0
    previous_word_dst: Optional[str] = None

    def fail(message: str, index: int) -> None:
        raise SchemeParseError(
            path=path,
            message=message,
            flat_text=text,
            flat_index=index,
            locations=locations,
            end_location=end_location,
        )

    while pos < len(text):
        open_pos: Optional[int] = None
        opener: Optional[str] = None

        for index in range(pos, len(text)):
            ch = text[index]
            if ch in ALL_CLOSE:
                fail(f"出现了没有对应左括号的 {ch}。", index)
            if ch in ALL_OPEN:
                open_pos = index
                opener = ch
                break

        if open_pos is None or opener is None:
            tail = text[pos:]
            if tail:
                fail(f"末尾存在没有括号的内容 {tail!r}。", pos)
            break

        raw_dst = text[pos:open_pos]
        inherited_word_dst = False

        if raw_dst:
            dst = raw_dst
        elif opener == "〖" and previous_word_dst is not None:
            # 例如 ab〖tr〗〖RF〗〖yu〗：后两个括号继承 ab。
            dst = previous_word_dst
            inherited_word_dst = True
        else:
            fail("此规则缺少括号外内容。", open_pos)

        closer = OPEN_TO_CLOSE[opener]
        close_pos = text.find(closer, open_pos + 1)
        if close_pos == -1:
            fail(f"左括号 {opener} 缺少对应的右括号 {closer}。", open_pos)

        src = text[open_pos + 1:close_pos]
        bad_bracket_index = next(
            (
                index
                for index in range(open_pos + 1, close_pos)
                if text[index] in ALL_BRACKETS
            ),
            None,
        )
        if bad_bracket_index is not None:
            fail("括号内部出现了嵌套或不配对括号。", bad_bracket_index)

        rule_number += 1
        if opener in ("［", "〔"):
            if len(dst) != 1:
                fail(
                    f"第 {rule_number} 条字转换规则左侧必须正好一个字符，"
                    f"实际读到 {dst!r}。",
                    pos,
                )
            if src == "":
                fail(f"第 {rule_number} 条字转换规则括号内为空。", open_pos)
            kind = "char"
            previous_word_dst = None
        elif opener == "〖":
            if src == "":
                fail(f"第 {rule_number} 条词语转换规则括号内为空。", open_pos)
            kind = "word"
            previous_word_dst = dst
        else:  # 〈〉：整条规则无意义，但保留以便回写字表。
            if len(dst) != 1:
                fail(
                    f"第 {rule_number} 条 〈〉 规则左侧必须正好一个字符，"
                    f"实际读到 {dst!r}。",
                    pos,
                )
            kind = "ignore"
            previous_word_dst = None

        rules.append(
            Rule(
                kind=kind,
                dst=dst,
                src=src,
                opener=opener,
                write_dst=not inherited_word_dst,
            )
        )
        pos = close_pos + 1

    return Scheme(path=path, rules=rules, repeat_enabled=repeat_enabled)


# ============================================================
# 字表标准化
# ============================================================

def ordered_unique_chars(text: str) -> list[str]:
    result: list[str] = []
    seen: set[str] = set()
    for ch in text:
        if ch not in seen:
            seen.add(ch)
            result.append(ch)
    return result


def normalize_scheme(scheme: Scheme) -> bool:
    """
    标准化字规则并处理冲突、连续简化。

    处理范围仅限 ``［］``、``〔〕`` 字规则：

    1. 同一目标的多条规则自动合并，并按首次出现顺序去重。
    2. 同一来源对应多个目标时，让用户用左右方向键选择唯一目标。
    3. 若某个中间目标本身还会继续简化，则把整条关系折叠到最终目标。
       例如 ``a［b］``、``c［a］`` 会写回为 ``c［ab］``。

    三类情况会反复检查直到稳定。``〖〗`` 词语规则和 ``〈〉`` 忽略
    规则不参与标准化，并在回写时原样保留。若连续简化关系形成循环，
    则明确报错，绝不无限运行或擅自选择结果。

    返回 True 表示字表内容发生改变，需要写回；False 表示无需改写。
    """
    original_char_rules = [
        (rule.dst, rule.src, rule.opener)
        for rule in scheme.rules
        if rule.kind == "char"
    ]

    target_order: list[str] = []
    sources_by_target: dict[str, list[str]] = {}
    opener_by_target: dict[str, str] = {}

    # 情况一：同一目标自动合并。混用两种字括号时，沿用首次出现的括号。
    for rule in scheme.rules:
        if rule.kind != "char":
            continue
        if rule.dst not in sources_by_target:
            target_order.append(rule.dst)
            sources_by_target[rule.dst] = []
            opener_by_target[rule.dst] = rule.opener
        sources_by_target[rule.dst] = ordered_unique_chars(
            "".join(sources_by_target[rule.dst]) + rule.src
        )

    def active_targets() -> list[str]:
        """返回仍有来源字符、最终会被写回的目标，保持字表顺序。"""
        return [target for target in target_order if sources_by_target[target]]

    def build_targets_by_source() -> tuple[dict[str, list[str]], list[str]]:
        """建立来源到目标的有序反向索引。"""
        targets_by_source: dict[str, list[str]] = {}
        source_order: list[str] = []
        for target in active_targets():
            for source_char in sources_by_target[target]:
                if source_char not in targets_by_source:
                    targets_by_source[source_char] = []
                    source_order.append(source_char)
                if target not in targets_by_source[source_char]:
                    targets_by_source[source_char].append(target)
        return targets_by_source, source_order

    def resolve_all_conflicts() -> bool:
        """处理当前状态下全部“一繁对多简”冲突。"""
        changed = False
        targets_by_source, source_order = build_targets_by_source()
        for source_char in source_order:
            candidates = [
                target
                for target in targets_by_source[source_char]
                if source_char in sources_by_target[target]
            ]
            if len(candidates) <= 1:
                continue

            chosen = choose_horizontal(source_char, candidates)
            for target in candidates:
                if target == chosen:
                    continue
                old_sources = sources_by_target[target]
                new_sources = [ch for ch in old_sources if ch != source_char]
                if new_sources != old_sources:
                    sources_by_target[target] = new_sources
                    changed = True
        return changed

    def parent_by_active_target() -> dict[str, str]:
        """
        返回“中间目标 -> 下一目标”。

        冲突已处理后，一个字符最多只能属于一个目标，因此每个中间目标
        至多有一个下一目标。
        """
        targets_by_source, _ = build_targets_by_source()
        active = set(active_targets())
        result: dict[str, str] = {}
        for target in active_targets():
            owners = targets_by_source.get(target, [])
            if owners:
                # owners 理论上只有一个；若未来代码改动破坏此前提，仍明确报错。
                if len(owners) > 1:
                    raise ValueError(
                        f"连续简化前仍存在未解决冲突：字符 {target!r} "
                        f"同时对应目标 {owners!r}。"
                    )
                parent = owners[0]
                if parent in active:
                    result[target] = parent
        return result

    def detect_continuous_cycle(parent_map: dict[str, str]) -> None:
        """检测目标依赖环，并给出可读的循环路径。"""
        done: set[str] = set()
        for start_target in target_order:
            if start_target not in parent_map or start_target in done:
                continue

            path: list[str] = []
            index_by_target: dict[str, int] = {}
            current = start_target
            while current in parent_map:
                if current in index_by_target:
                    cycle = path[index_by_target[current]:] + [current]
                    rendered = " -> ".join(cycle)
                    raise ValueError(
                        "连续简化规则形成循环，无法确定最终目标："
                        f"{rendered}。请修改字表后重试。"
                    )
                if current in done:
                    break
                index_by_target[current] = len(path)
                path.append(current)
                current = parent_map[current]
            done.update(path)

    def collapse_one_continuous_relation() -> bool:
        """
        折叠一层连续简化关系。

        若 child 的规则为 ``child［xy］``，而 parent 的来源中含 child，
        则在 parent 中保留 child，并紧接着插入 x、y；随后删除 child
        自己的规则。逐层执行可自然保持以下顺序：

            a［bd］ c［ax］ e［c］  ->  e［cabdx］
        """
        parent_map = parent_by_active_target()
        detect_continuous_cycle(parent_map)

        for child in target_order:
            parent = parent_map.get(child)
            if parent is None:
                continue

            child_sources = sources_by_target[child]
            parent_sources = sources_by_target[parent]
            try:
                bridge_index = parent_sources.index(child)
            except ValueError as exc:  # 防御性检查
                raise ValueError(
                    f"连续简化内部状态异常：目标 {parent!r} 的来源中找不到 {child!r}。"
                ) from exc

            expanded = (
                parent_sources[:bridge_index + 1]
                + child_sources
                + parent_sources[bridge_index + 1:]
            )
            sources_by_target[parent] = ordered_unique_chars("".join(expanded))
            sources_by_target[child] = []
            return True
        return False

    # 情况二与连续简化可以交错出现，因此循环到完全稳定。
    # 每轮先消除冲突，再折叠一层连续关系；折叠后回到循环顶部重新检查。
    while True:
        conflict_changed = resolve_all_conflicts()
        continuous_changed = collapse_one_continuous_relation()
        if continuous_changed:
            continue
        if not conflict_changed:
            break
        # 仅发生冲突修改时再检查一次，确认没有新链或新冲突。

    normalized_char_rules: list[Rule] = []
    for target in target_order:
        sources = sources_by_target[target]
        if not sources:
            continue
        normalized_char_rules.append(
            Rule(
                kind="char",
                dst=target,
                src="".join(sources),
                opener=opener_by_target[target],
            )
        )

    # 把全部标准化字规则放回“第一条原字规则”的位置；
    # 词语和 〈〉 规则的相对顺序保持不变。
    rebuilt: list[Rule] = []
    inserted_char_block = False
    had_char_rule = any(rule.kind == "char" for rule in scheme.rules)

    for rule in scheme.rules:
        if rule.kind == "char":
            if not inserted_char_block:
                rebuilt.extend(normalized_char_rules)
                inserted_char_block = True
            continue
        rebuilt.append(rule)

    if not had_char_rule and normalized_char_rules:
        rebuilt = normalized_char_rules + rebuilt

    new_char_rules = [
        (rule.dst, rule.src, rule.opener)
        for rule in rebuilt
        if rule.kind == "char"
    ]

    changed = original_char_rules != new_char_rules
    scheme.rules = rebuilt
    return changed

def write_scheme(scheme: Scheme) -> None:
    """以 UTF-8 写回标准化字表；连续 〖〗 保持在同一目标词后。"""
    lines: list[str] = []
    if scheme.repeat_enabled:
        # 指令不参与规则解析，但标准化回写后必须保留。
        lines.append(REPEAT_DIRECTIVE)
    for rule in scheme.rules:
        serialized = rule.serialize()
        if rule.kind == "word" and not rule.write_dst and lines:
            lines[-1] += serialized
        else:
            lines.append(serialized)

    content = "\n".join(lines)
    if content:
        content += "\n"
    with scheme.path.open("w", encoding="utf-8", newline="\n") as file:
        file.write(content)


# ============================================================
# 最长词匹配与转换
# ============================================================

class TrieNode:
    __slots__ = ("children", "replacement")

    def __init__(self) -> None:
        self.children: dict[str, TrieNode] = {}
        self.replacement: Optional[str] = None


class WordTrie:
    def __init__(self, rules: Iterable[Rule]) -> None:
        self.root = TrieNode()
        for rule in rules:
            if rule.kind != "word":
                continue
            self.add(rule.src, rule.dst)

    def add(self, source: str, target: str) -> None:
        node = self.root
        for ch in source:
            node = node.children.setdefault(ch, TrieNode())
        # 同一来源词重复出现时，保留字表中先出现的转换。
        if node.replacement is None:
            node.replacement = target

    def replace_longest(self, text: str) -> str:
        output: list[str] = []
        i = 0

        while i < len(text):
            node = self.root
            j = i
            best_end = -1
            best_replacement: Optional[str] = None

            while j < len(text):
                child = node.children.get(text[j])
                if child is None:
                    break
                node = child
                j += 1
                if node.replacement is not None:
                    best_end = j
                    best_replacement = node.replacement

            if best_replacement is None:
                output.append(text[i])
                i += 1
            else:
                output.append(best_replacement)
                i = best_end

        return "".join(output)


def is_western_character(ch: str) -> bool:
    """
    判断一个字符是否属于这里所说的“西文”。

    ASCII、拉丁字母、IPA/拉丁扩展字符，以及规范化后变成 ASCII
    字母或数字的全角形式，都视为西文，不参加叠字符替换。
    """
    codepoint = ord(ch)
    if codepoint <= 0x02FF:
        return True

    name = unicodedata.name(ch, "")
    if any(script in name for script in ("LATIN", "GREEK", "CYRILLIC")):
        return True

    normalized = unicodedata.normalize("NFKC", ch)
    return len(normalized) == 1 and normalized.isascii() and normalized.isalnum()


def is_repeat_eligible(ch: str) -> bool:
    """
    判断连续重复字符是否可用“𠚤”代替。

    Unicode 私用区字符的类别是 ``Co``。本程序按用户字表的约定，
    把基本私用区、补充私用区 A 和补充私用区 B 中的字符都视作
    可参与叠字符转换的汉字。其他 C 类字符（控制字符、格式字符、
    代理项和未分配字符）仍然排除。
    """
    category = unicodedata.category(ch)

    # Co = Private Use。必须在排除全部 C 类字符之前单独放行。
    if category == "Co":
        return True

    if category.startswith("P"):
        return False
    if category.startswith("Z") or category.startswith("C"):
        return False
    if is_western_character(ch):
        return False
    return True


def replace_repeated_characters(text: str) -> str:
    """
    把连续的、符合条件的同一字符从第二个起替换为“𠚤”。

    比较依据始终是转换后的原字符序列，而不是已经写入输出的标记，
    因而“哈哈哈哈”会得到“哈𠚤𠚤𠚤”。
    """
    if not text:
        return text

    output: list[str] = [text[0]]
    previous = text[0]
    for ch in text[1:]:
        if ch == previous and is_repeat_eligible(ch):
            output.append(REPEAT_MARK)
        else:
            output.append(ch)
        previous = ch
    return "".join(output)


class Converter:
    def __init__(self, scheme: Scheme) -> None:
        self.word_trie = WordTrie(scheme.word_rules)
        self.char_map: dict[str, str] = {}
        self.repeat_enabled = scheme.repeat_enabled

        for rule in scheme.char_rules:
            for source_char in rule.src:
                self.char_map[source_char] = rule.dst

    def convert_text(self, text: str) -> str:
        # 严格按照需求：先词语、后单字，最后才处理叠字符。
        after_words = self.word_trie.replace_longest(text)
        after_chars = "".join(self.char_map.get(ch, ch) for ch in after_words)
        if self.repeat_enabled:
            return replace_repeated_characters(after_chars)
        return after_chars

    def convert_file(self, source_path: Path, output_path: Path) -> None:
        try:
            # 直接解码字节，避免文本模式把 CRLF 自动改成 LF。
            text = source_path.read_bytes().decode("utf-8-sig")
        except UnicodeDecodeError as exc:
            raise ValueError(f"{source_path.name} 不是有效的 UTF-8 文件。") from exc

        converted = self.convert_text(text)
        output_path.write_bytes(converted.encode("utf-8"))


# ============================================================
# 主流程
# ============================================================

def find_text_files() -> list[Path]:
    return sorted(
        (
            path
            for path in BASE_DIR.iterdir()
            if path.is_file() and path.suffix.lower() == ".txt"
        ),
        key=lambda path: path.name.casefold(),
    )


def print_program_header() -> None:
    """打印版本和实际脚本路径，避免误运行旧的同名文件。"""
    print(f"简化字转换程序 v{PROGRAM_VERSION}")
    print(f"正在运行：{Path(__file__).resolve()}")
    print()


def run() -> int:
    print_program_header()
    scheme_files = find_scheme_files()
    if not scheme_files:
        print(f"未找到转换字表。请把字表放入：{CODE_DIR}")
        print("字表名必须是 4 位年份，可选再加 1 位大写字母，例如 1977.wzgg、1977A.wzgg。")
        return 1

    if len(scheme_files) == 1:
        selected_path = scheme_files[0]
    else:
        selected_index = choose_vertical(
            "请选择转换方案",
            [path.stem for path in scheme_files],
        )
        selected_path = scheme_files[selected_index]

    clear_screen()
    print_program_header()
    print(f"正在载入字表：{selected_path.name}")
    scheme = parse_scheme(selected_path)

    changed = normalize_scheme(scheme)
    if changed:
        write_scheme(scheme)
        print(f"字表已标准化并写回：{selected_path.name}")
    else:
        print("字表无需修改。")

    text_files = find_text_files()
    if not text_files:
        print(f"程序目录中没有找到 .txt 文件：{BASE_DIR}")
        return 0

    converter = Converter(scheme)
    print(f"\n使用方案：{selected_path.stem}")
    print(f"找到 {len(text_files)} 个 TXT 文件。\n")

    failed = 0
    for source_path in text_files:
        output_name = f"{source_path.stem}（{selected_path.stem}）.wzgg"
        output_path = source_path.with_name(output_name)
        try:
            converter.convert_file(source_path, output_path)
            print(f"完成：{source_path.name} -> {output_path.name}")
        except (OSError, ValueError) as exc:
            failed += 1
            print(f"失败：{source_path.name}：{exc}")

    if failed:
        print(f"\n转换结束：{len(text_files) - failed} 个成功，{failed} 个失败。")
        return 1

    print(f"\n转换结束：全部 {len(text_files)} 个文件已完成。")
    return 0


def main() -> None:
    try:
        exit_code = run()
    except UserCancelled:
        clear_screen()
        print_program_header()
        print("已取消。")
        exit_code = 0
    except SchemeParseError as exc:
        # 单独处理字表格式错误，确保详细位置不会被简化成一句话。
        report = (
            f"简化字转换程序 v{PROGRAM_VERSION}\n"
            f"正在运行：{Path(__file__).resolve()}\n\n"
            f"字表解析失败：\n{exc}\n"
        )
        print("\n" + "=" * 68)
        print(report, end="")
        print("=" * 68)
        try:
            ERROR_REPORT_PATH.write_text(report, encoding="utf-8")
            print(f"错误报告已保存到：{ERROR_REPORT_PATH}")
        except OSError as report_error:
            print(f"错误报告无法写入文件：{report_error}")
        exit_code = 1
    except (OSError, ValueError) as exc:
        print(f"错误：{exc}")
        exit_code = 1
    except KeyboardInterrupt:
        print("\n已取消。")
        exit_code = 0

    raise SystemExit(exit_code)


if __name__ == "__main__":
    main()
