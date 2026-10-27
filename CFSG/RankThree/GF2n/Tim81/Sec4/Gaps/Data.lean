module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Check

public section

namespace CFSG.RankThree.GF2n.Tim81.Gaps

open CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck

@[expose] def a6tA : Table := #[1, 2, 0, 3, 4, 5]

@[expose] def a6tAi : Table := #[2, 0, 1, 3, 4, 5]

@[expose] def a6tB : Table := #[0, 2, 3, 4, 5, 1]

@[expose] def a6tBi : Table := #[0, 5, 1, 2, 3, 4]

@[expose] def a6gens (l : Int) : Table :=
  if l = 1 then a6tA else if l = -1 then a6tAi else if l = 2 then a6tB else
    if l = -2 then a6tBi else idT 6

@[expose] def a6pc : List (List Int) :=
  [[1, 2, -1, 2, 2], [-1, -2, -1, -2], [2, -1, 2, 2, 1, -2, 1, -2, -2]]

@[expose] def a6cls : List (List (Nat × List Int)) :=
  [[(2, []), (6, [1, -2, 1, 2, 2, -1, -2])],
    [(3, []), (7, [-1, -2, -1, -2])]]

@[expose] def a6gv : List (List Bool × GVerdict) :=
  [([false, false], .small),
    ([true, false], .solv [-2, 1, 2, 1, -2] 3 1),
    ([false, true], .solv [-1, -2, 1, -2, -1, 2, 2] 3 1),
    ([true, true], .notClosed 2 3)]

@[expose] def a6GData : GData where
  D := { n := 6, gens := a6gens, pc := a6pc, zIdx := 4, cw := [], cls := a6cls, verdicts := [] }
  fuel := 64
  gv := a6gv

end CFSG.RankThree.GF2n.Tim81.Gaps
