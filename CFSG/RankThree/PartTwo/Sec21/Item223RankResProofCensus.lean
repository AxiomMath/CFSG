module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofAll

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem outer223High_of_rank
    (hD4 : TrialityD4EvenThreeRankTwo) (hF4 : TwistedF4EvenThreeRankTwo) : Outer223High :=
  outer223High_of g2OddThreeRankTwo_holds (excEvenThreeRankTwo_of hD4 hF4)

section Census

theorem inspection223List_of_rank (hD4 : TrialityD4EvenThreeRankTwo)
    (hF4 : TwistedF4EvenThreeRankTwo) : Inspection223List :=
  inspection223List_of_res g2OddThreeRankTwo_holds (excEvenThreeRankTwo_of hD4 hF4)

end Census

end CFSG.RankThree.PartTwo.Sec21
