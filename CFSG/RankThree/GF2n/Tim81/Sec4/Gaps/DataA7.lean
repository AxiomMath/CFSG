module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Check

public section

namespace CFSG.RankThree.GF2n.Tim81.Gaps

open CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck

@[expose] def a7tA : Table := #[1, 2, 0, 3, 4, 5, 6]
@[expose] def a7tAi : Table := #[2, 0, 1, 3, 4, 5, 6]
@[expose] def a7tB : Table := #[1, 2, 3, 4, 5, 6, 0]
@[expose] def a7tBi : Table := #[6, 0, 1, 2, 3, 4, 5]
@[expose] def a7gens (l : Int) : Table :=
  if l = 1 then a7tA else if l = -1 then a7tAi else if l = 2 then a7tB else
    if l = -2 then a7tBi else idT 7

@[expose] def a7pc : List (List Int) := [
  [-2, -2, -1, -1, 2, 2, 2, -1, -2, -1, -2, -2, -1, 2, 2],
  [2, 1, -2, -1, 2, 2, 1, -2, -1, 2],
  [1, 2, 1, 2, 1, 2, 1, -2, -2, -1, -2, -2, -1, 2, 2, 1]
]

@[expose] def a7cls : List (List (Nat × List Int)) := [
  [
    (1, []),
    (5, [2, 1, -2, -1, 2, 2, 1, -2, -1, 2])
  ],
  [
    (2, []),
    (6, [2, 1, -2, 1, -2, -2, -1, 2, 1, 2, -1])
  ]
]

@[expose] def a7gv : List (List Bool × GVerdict) := [
  ([false, false], .small), ([true, false], .solv [2] 3 1), ([false, true], .solv [1] 2 1),
  ([true, true], .notClosed 1 2)
]

@[expose] def a7Data : Data where
  n := 7
  gens := a7gens
  pc := a7pc
  zIdx := 4
  cw := []
  cls := a7cls
  verdicts := []

@[expose] def a7GData : GData where
  D := a7Data
  fuel := 128
  gv := a7gv

end CFSG.RankThree.GF2n.Tim81.Gaps
