module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Check

public section

namespace CFSG.RankThree.GF2n.Tim81.Gaps

open CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck

@[expose] def a9tA : Table := #[1, 2, 0, 3, 4, 5, 6, 7, 8]
@[expose] def a9tAi : Table := #[2, 0, 1, 3, 4, 5, 6, 7, 8]
@[expose] def a9tB : Table := #[1, 2, 3, 4, 5, 6, 7, 8, 0]
@[expose] def a9tBi : Table := #[8, 0, 1, 2, 3, 4, 5, 6, 7]
@[expose] def a9gens (l : Int) : Table :=
  if l = 1 then a9tA else if l = -1 then a9tAi else if l = 2 then a9tB else
    if l = -2 then a9tBi else idT 9

@[expose] def a9pc : List (List Int) := [
  [
    -1,
    2,
    -1,
    -1,
    2,
    -1,
    -2,
    -2,
    -2,
    1,
    2,
    2,
    1,
    -2,
    -2,
    -2,
    -2,
    1,
    -2,
    -2,
    -1,
    2,
    2,
    -1,
    -2,
    1,
    2,
    2
  ],
  [-1, -2, -1, 2, 2, -1, 2, 2, -1, -2, -2, -1, -2, 1, -2, -2, -1, 2, 2, -1, 2],
  [2, 2, -1, -2, -1, -1, 2, -1, -1, -2, -2, -1, -2, -2, 1, 2, 1, 2],
  [2, 2, -1, 2, 2, 2, 1, -2, -2, -2, -1, -2, 1, -2, -2, -1, 2, -1, 2, 2],
  [
    -2,
    -2,
    -2,
    1,
    -2,
    -2,
    1,
    2,
    2,
    1,
    -2,
    -2,
    1,
    2,
    2,
    1,
    -2,
    -2,
    -2,
    -2,
    1,
    -2,
    -2,
    -1,
    2,
    -1,
    2,
    -1,
    2
  ],
  [-2, -2, -2, 1, 1, 2, -1, -2, -2, -1, -2, -2, -2, 1, 2, 2, 2]
]

@[expose] def a9cls : List (List (Nat × List Int)) := [
  [
    (1, []),
    (6, [2, -1, -2, -1, -2, -2, -2, -1, 2, 1, 2, 1, 2]),
    (
      38,
      [-2, -2, -2, 1, 2, 2, 1, 2, 2, -1, 2, 2, 1, 2, 1, -2, -2, -2, -1, -2, -2, -1, 2, -1, 2]
    ),
    (7, [-2, -2, -2, -1, 2, 2, 2, 2, 2, -1, -2, -2]),
    (
      33,
      [
        -2,
        1,
        2,
        -1,
        2,
        2,
        -1,
        2,
        2,
        1,
        -2,
        1,
        1,
        2,
        2,
        1,
        -2,
        -2,
        -2,
        -2,
        -1,
        -2,
        -2,
        -1,
        2,
        2,
        -1,
        -2,
        1,
        2,
        2
      ]
    ),
    (39, [-2, -2, 1, 2, -1, 2, 2, -1, 2, 2, 1, 2, 1, -2, -2, -2, -1, -2, -1, -2, 1, 2, -1, 2])
  ],
  [
    (2, []),
    (
      4,
      [
        -1,
        2,
        -1,
        -1,
        2,
        -1,
        -2,
        -2,
        -2,
        1,
        2,
        2,
        1,
        -2,
        -2,
        -2,
        -2,
        1,
        -2,
        -2,
        -1,
        2,
        2,
        -1,
        -2,
        1,
        2,
        2
      ]
    ),
    (58, [2, 2, -1, 2, 2, 2, 1, -2, -2, -2, -1, -2, 1, -2, -2, -1, 2, -1, 2, 2]),
    (
      28,
      [
        -1,
        -1,
        -2,
        -2,
        1,
        -2,
        -1,
        2,
        -1,
        -2,
        -2,
        -2,
        -2,
        1,
        -2,
        -2,
        -1,
        2,
        2,
        -1,
        -2,
        1,
        2,
        -1,
        2
      ]
    )
  ],
  [
    (8, []),
    (24, [2, -1, -2, -1, -2, -2, -2, -1, 2, 1, 2, 1, 2]),
    (48, [-2, -2, -1, -2, -1, 2, 2, 2, 1, 2, 2, 1, -2, -2, 1, -2]),
    (16, [-2, -2, -2, -1, 2, 2, 2, 2, 2, -1, -2, -2]),
    (56, [-2, -1, 2, 1, 2, 2, 1, -2, -1, -2, -2, -1, 2, 1, -2, 1]),
    (40, [2, 2, 1, -2, 1, 2, 2, -1, -2, -2, -1, -2, 1, -2, -2, -1, 2, 1, 2, 1, 2])
  ],
  [
    (9, []),
    (30, [2, -1, -2, -1, -2, -2, -2, -1, 2, 1, 2, 1, 2]),
    (
      62,
      [-2, -2, -2, 1, 2, 2, 1, 2, 2, -1, 2, 2, 1, 2, 1, -2, -2, -2, -1, -2, -2, -1, 2, -1, 2]
    ),
    (55, [-2, -2, 1, 2, -1, 2, 2, -1, 2, 2, 1, 2, 1, -2, -2, -2, -1, -2, -1, -2, 1, 2, -1, 2]),
    (
      41,
      [
        -2,
        1,
        2,
        -1,
        2,
        2,
        -1,
        2,
        2,
        1,
        -2,
        1,
        1,
        2,
        2,
        1,
        -2,
        -2,
        -2,
        -2,
        -1,
        -2,
        -2,
        -1,
        2,
        2,
        -1,
        -2,
        1,
        2,
        2
      ]
    ),
    (23, [-2, -2, -2, -1, 2, 2, 2, 2, 2, -1, -2, -2])
  ],
  [
    (26, []),
    (
      60,
      [
        -1,
        2,
        -1,
        -1,
        2,
        -1,
        -2,
        -2,
        -2,
        1,
        2,
        2,
        1,
        -2,
        -2,
        -2,
        -2,
        1,
        -2,
        -2,
        -1,
        2,
        2,
        -1,
        -2,
        1,
        2,
        2
      ]
    ),
    (34, [2, 2, -1, 2, 2, 2, 1, -2, -2, -2, -1, -2, 1, -2, -2, -1, 2, -1, 2, 2]),
    (
      36,
      [
        -1,
        -1,
        -2,
        -2,
        1,
        -2,
        -1,
        2,
        -1,
        -2,
        -2,
        -2,
        -2,
        1,
        -2,
        -2,
        -1,
        2,
        2,
        -1,
        -2,
        1,
        2,
        -1,
        2
      ]
    )
  ]
]

@[expose] def a9gv : List (List Bool × GVerdict) := [
  ([false, false, false, false, false], .small),
  ([true, false, false, false, false], .solv [-1, 2] 5 1),
  ([false, true, false, false, false], .notClosed 32 2),
  ([true, true, false, false, false], .notClosed 32 2),
  ([false, false, true, false, false], .solv [1, 2, 1] 4 1),
  ([true, false, true, false, false], .notClosed 1 8),
  ([false, true, true, false, false], .notClosed 32 2),
  ([true, true, true, false, false], .notClosed 32 2),
  ([false, false, false, true, false], .solv [-1, 2] 5 1),
  ([true, false, false, true, false], .notClosed 1 9),
  ([false, true, false, true, false], .notClosed 32 2),
  ([true, true, false, true, false], .notClosed 32 2),
  ([false, false, true, true, false], .notClosed 8 9),
  ([true, false, true, true, false], .notClosed 1 24),
  ([false, true, true, true, false], .notClosed 32 2),
  ([true, true, true, true, false], .notClosed 32 2),
  ([false, false, false, false, true], .notClosed 32 26),
  ([true, false, false, false, true], .notClosed 32 26),
  ([false, true, false, false, true], .notClosed 2 4),
  ([true, true, false, false, true], .notClosed 1 2),
  ([false, false, true, false, true], .notClosed 32 26),
  ([true, false, true, false, true], .notClosed 32 26),
  ([false, true, true, false, true], .notClosed 2 4),
  ([true, true, true, false, true], .notClosed 1 2),
  ([false, false, false, true, true], .notClosed 32 26),
  ([true, false, false, true, true], .notClosed 32 26),
  ([false, true, false, true, true], .notClosed 2 4),
  ([true, true, false, true, true], .notClosed 1 2),
  ([false, false, true, true, true], .notClosed 32 26),
  ([true, false, true, true, true], .notClosed 32 26),
  ([false, true, true, true, true], .notClosed 2 4),
  ([true, true, true, true, true], .notClosed 1 2)
]

@[expose] def a9Data : Data where
  n := 9
  gens := a9gens
  pc := a9pc
  zIdx := 32
  cw := []
  cls := a9cls
  verdicts := []

@[expose] def a9GData : GData where
  D := a9Data
  fuel := 128
  gv := a9gv

end CFSG.RankThree.GF2n.Tim81.Gaps
