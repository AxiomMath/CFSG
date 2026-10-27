module

public import CFSG.RankThree.PartTwo.Sec17.Ronan1712Q8
public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofWire

public section

namespace CFSG.RankThree.PartTwo.Sec17.Ronan1712Q8

open CFSG.RankThree.PartTwo.Sec17
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

section Wire

theorem step1712DeltaF_of_res14_faith (hFaith : Step1712Faith) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (h176 : Item176R) (hbal : Step143Balance)
    (h143 : Ronan148Q.Item143QS14) (h166 : Item166S17)
    (hbot : Item145BotS17) (h168 : Item168S17) (h146 : Item146S14) (h172 : Item172S17)
    (h9 : CardInfNineS17) (h165 : Item165S17) (hQ0 : Claim17Q0) (hI : Claim174Inner)
    (hKbO : Step174KbO) : Step1712DeltaF :=
  step1712DeltaF_of_q8 (step1712DeltaQ8_of_faith hFaith h143) h1514 hMeets hFaith h176 hbal
    (sec17OThreeSolv_of_res14 h166 hbot h168 h146 h172 h9 h165 hQ0 hI hKbO)

end Wire

end CFSG.RankThree.PartTwo.Sec17.Ronan1712Q8
