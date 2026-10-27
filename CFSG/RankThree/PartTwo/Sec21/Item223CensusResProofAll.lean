module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofSpor
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofAll
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCharThree

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem inspection223List_of_res (hG2 : G2OddThreeRankTwo) (hExc : ExcEvenThreeRankTwo) :
    Inspection223List :=
  inspection223List_of_facts (census223RankTwoOddRest_of hG2) (census223RankTwoEvenRest_of hExc)
    census223McLONOrders_holds census223Sp62Orders_holds census223CharThreeOrders_holds
    (outer223High_of hG2 hExc) outer223Cross_holds

end CFSG.RankThree.PartTwo.Sec21
