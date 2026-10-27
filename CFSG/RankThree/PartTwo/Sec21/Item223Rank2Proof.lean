module

public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofCensus

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem outer223High_of_twistedF4
    (hF4 : TwistedF4EvenThreeRankTwo) : Outer223High :=
  outer223High_of_rank trialityD4EvenThreeRankTwo_holds hF4

section Census

theorem inspection223List_of_twistedF4 (hF4 : TwistedF4EvenThreeRankTwo) : Inspection223List :=
  inspection223List_of_rank trialityD4EvenThreeRankTwo_holds hF4

end Census

end CFSG.RankThree.PartTwo.Sec21
