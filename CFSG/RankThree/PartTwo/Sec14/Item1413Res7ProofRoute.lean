module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofOdd

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

theorem item1413CR_of_res7
    (h131 : Item131) (h142All : Item142AllS14)
    (h142 : Concl142S14) (h146 : Item146S14) (hbot : Item145BotS14) : Item1413CR :=
  item1413CR_of h131 h142All h142 h146 hbot (item1413CL3R_of_res7 h131 h142All hbot)

end CFSG.RankThree.PartTwo.Sec14
