module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Check

public section

namespace CFSG.RankThree.GF2n.Tim81.Gaps

open CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck

@[expose] def a8tA : Table := #[1, 2, 0, 3, 4, 5, 6, 7]
@[expose] def a8tAi : Table := #[2, 0, 1, 3, 4, 5, 6, 7]
@[expose] def a8tB : Table := #[0, 2, 3, 4, 5, 6, 7, 1]
@[expose] def a8tBi : Table := #[0, 7, 1, 2, 3, 4, 5, 6]
@[expose] def a8gens (l : Int) : Table :=
  if l = 1 then a8tA else if l = -1 then a8tAi else if l = 2 then a8tB else
    if l = -2 then a8tBi else idT 8

@[expose] def a8pc : List (List Int) := [
  [1, 1, -2, -1, -2, 1, 2, 2, 1, -2, -2, -2, -2, -2, -1, 2, -1, 2, -1, 2],
  [-2, -2, 1, 2, -1, 2],
  [2, -1, 2, -1, -2, -2, -2, -2, -1, 2, 2, -1, 2],
  [2, 2, 2, -1, -2, 1, 2, 1, -2, -2, 1, -2, -2, -2, -1, 2, 2, -1, 2],
  [2, 2, 2, -1, -2, -1, -2, -2, -1, -2, -2, -1, 2, 2, -1, -2, -1, 2, -1, 2],
  [2, 2, 2, -1, -2, 1, 2, 1, -2, -2, 1, -2, -2, -2, -1, 2, 1, 2, 1, 2]
]

@[expose] def a8cls : List (List (Nat × List Int)) := [
  [
    (1, []),
    (6, [-1, -2, -2, -2, 1, 2, -1, 2, -1, 2]),
    (7, [2, -1, 2, -1, -2, -2, -2, -2, -1, 2, 2, -1, 2]),
    (39, [2, 2, -1, -2, 1, 2, 2, 1, -2, -2, -2, -2, -2, -1, 2, 2, -1, 2]),
    (38, [-2, -1, -2, 1, 2, 1, -2, -2, -1, 2, 2, 2, -1, 2, 2, -1, -2, 1, -2, 1]),
    (33, [2, 2, 2, -1, -2, 1, 2, 1, -2, -2, 1, -2, -2, -2, -1, 2, 2, -1, 2])
  ],
  [
    (2, []),
    (42, [2, -1, 2, 1, -2, -2, 1, -2, -2, -1, 2, -1, 2]),
    (4, [1, 1, -2, -1, -2, 1, 2, 2, 1, -2, -2, -2, -2, -2, -1, 2, -1, 2, -1, 2]),
    (12, [-2, -2, -1, -2, -2, -2, -2, -1, 2, -1, 2, 1, 2])
  ],
  [
    (8, []),
    (48, [-2, -2, -1, -2, -1, 2, 2, 2, 1]),
    (24, [-1, -2, -2, -2, 1, 2, -1, 2, -1, 2]),
    (56, [-2, -2, -2, -1, 2, 2, 2, 2, 2, -1, -2, -2, -1, 2, 1, 2, 1, 2, 1, -2]),
    (16, [-1, 2, 2, 1, -2, -1, -2, -2, -1, 2, 2]),
    (40, [1, 1, -2, -1, -2, 1, 2, 2, 1, -2, -2, -2, -2, -2, -1, 2, -1, 2, -1, 2])
  ],
  [
    (10, []),
    (34, [2, -1, 2, 1, -2, -2, 1, -2, -2, -1, 2, -1, 2]),
    (44, [1, 1, -2, -1, -2, 1, 2, 2, 1, -2, -2, -2, -2, -2, -1, 2, -1, 2, -1, 2]),
    (36, [-2, -2, -1, -2, -2, -2, -2, -1, 2, -1, 2, 1, 2])
  ],
  [
    (14, []),
    (55, [-1, 2, 1, 2, 1, 2, 1, -2, -2, 1, -2, -2, -1, 2, 2]),
    (23, [-1, 2, 2, 1, -2, -1, -2, -2, -1, 2, 2]),
    (25, [-1, -2, -2, -2, 1, 2, -1, 2, -1, 2]),
    (46, [2, -1, 2, 1, -2, -2, 1, -2, -2, -1, 2, -1, 2]),
    (57, [-1, 2, -1, 2, 1, -2, -2, 1, -2, -2, -2, 1, 2, 2, -1, -2, -1, 2, 1, 2])
  ]
]

@[expose] def a8gv : List (List Bool × GVerdict) := [
  ([false, false, false, false, false], .small),
  ([true, false, false, false, false], .solv [1] 5 1),
  ([false, true, false, false, false], .notClosed 32 2),
  ([true, true, false, false, false], .notClosed 32 2),
  ([false, false, true, false, false], .solv [1, 2, -1] 5 1),
  ([true, false, true, false, false], .notClosed 1 8),
  ([false, true, true, false, false], .notClosed 32 2),
  ([true, true, true, false, false], .notClosed 32 2),
  ([false, false, false, true, false], .notClosed 32 10),
  ([true, false, false, true, false], .notClosed 32 10),
  ([false, true, false, true, false], .notClosed 2 42),
  ([true, true, false, true, false], .notClosed 1 2),
  ([false, false, true, true, false], .notClosed 32 10),
  ([true, false, true, true, false], .notClosed 32 10),
  ([false, true, true, true, false], .notClosed 2 4),
  ([true, true, true, true, false], .notClosed 1 2),
  ([false, false, false, false, true], .solv [1] 5 1),
  ([true, false, false, false, true], .notClosed 1 14),
  ([false, true, false, false, true], .notClosed 32 2),
  ([true, true, false, false, true], .notClosed 32 2),
  ([false, false, true, false, true], .notClosed 8 14),
  ([true, false, true, false, true], .notClosed 1 8),
  ([false, true, true, false, true], .notClosed 32 2),
  ([true, true, true, false, true], .notClosed 32 2),
  ([false, false, false, true, true], .notClosed 32 10),
  ([true, false, false, true, true], .notClosed 32 10),
  ([false, true, false, true, true], .notClosed 2 42),
  ([true, true, false, true, true], .notClosed 1 2),
  ([false, false, true, true, true], .notClosed 32 10),
  ([true, false, true, true, true], .notClosed 32 10),
  ([false, true, true, true, true], .notClosed 2 4),
  ([true, true, true, true, true], .notClosed 1 2)
]

@[expose] def a8Data : Data where
  n := 8
  gens := a8gens
  pc := a8pc
  zIdx := 32
  cw := []
  cls := a8cls
  verdicts := []

@[expose] def a8GData : GData where
  D := a8Data
  fuel := 128
  gv := a8gv

end CFSG.RankThree.GF2n.Tim81.Gaps
