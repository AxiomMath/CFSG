module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432WitCheck
public import Certificates.Data.Item434D42

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec4.Item434D42

@[expose] def d4WitData : WitData where
  n := 2457
  gens := #[d4GenA, d4GenB]
  nGens := 2
  pW := (#["AAbABBAbAbbAAbaaBBBABA",
      "BaBaBaabABABABaababAAABBabbababAbbbABAABABaBaaabaaaBaaaa",
      "bababABABABaabaBAA",
      "BBBABBBBBBaBBaaababbababbbABBAbAABABBAAA"]).map parseSigned
  pKeys := [0, 1]
  pFuel := 90
  pOrd := 81
  qW := (#["AAbABBAbAbbAAbaaBBBABA",
      "BaBaBaabABABABaababAAABBabbababAbbbABAABABaBaaabaaaBaaaa",
      "bababABABABaabaBAA",
      "BBBABBBBBBaBBaaababbababbbABBAbAABABBAAA"]).map parseSigned
  qKeys := [0, 1]
  qFuel := 90
  yW := (#["aBaBBBaB"]).map parseSigned

end CFSG.RankThree.PartTwo.Sec4.RonanK432
