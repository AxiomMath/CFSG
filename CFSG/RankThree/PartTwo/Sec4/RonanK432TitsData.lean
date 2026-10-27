module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432WitCheck
public import CFSG.Sporadic.Schreier.TitsArrays

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Sporadic.Schreier.Tits

@[expose] def titsWitData : WitData where
  n := 1755
  gens := #[titsDerivedArrs[0]!, titsDerivedArrs[1]!]
  nGens := 2
  pW := #[[1, -2, -2, -1],
      [2, 1, 1, -2, 1, 2, 2, -1, -2, -2, 1, -2, -2, -1, 2, -1, -1, -2]]
  pKeys := [0]
  pFuel := 40
  pOrd := 27
  qW := #[[1, -2, -2, -1],
      [2, 1, 1, -2, 1, 2, 2, -1, -2, -2, 1, -2, -2, -1, 2, -1, -1, -2]]
  qKeys := [0]
  qFuel := 40
  yW := #[[-2, 1, 1, 2, -1, -1, -1, 2, 2, -1, -2, 1, -2, 1, -2, 1, 1, 2, -1, 2, -1, -2, -2, 1, -2, -2, -1, 2, 2]]

end CFSG.RankThree.PartTwo.Sec4.RonanK432
