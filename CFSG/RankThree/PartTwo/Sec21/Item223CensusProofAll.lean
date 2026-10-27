module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOuterLin
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofA9
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOrders
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofSymp

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem innerCensus223_of_facts (hOdd : Census223RankTwoOddRest)
    (hEven : Census223RankTwoEvenRest) (hSpor : Census223McLONOrders)
    (hSp62 : Census223Sp62Orders) (hThree : Census223CharThreeOrders) : InnerCensus223 :=
  innerCensus223_of (census223RankTwoOdd_of hOdd) (census223RankTwoEven_of hEven)
    census223A9_holds (census223Sporadic_of (census223SporadicRest_of hSpor))
    (census223Sp62_of hSp62) (census223CharThree_of (census223CharThreeRest_of hThree))

theorem inspection223List_of_facts (hOdd : Census223RankTwoOddRest)
    (hEven : Census223RankTwoEvenRest) (hSpor : Census223McLONOrders)
    (hSp62 : Census223Sp62Orders) (hThree : Census223CharThreeOrders) (hHigh : Outer223High)
    (hCross : Outer223Cross) : Inspection223List :=
  inspection223List_of
    (inspection223ListInner_of_census (innerCensus223_of_facts hOdd hEven hSpor hSp62 hThree))
    (inspection223ListOuter_of (outer223Linear_of hHigh hCross))

end CFSG.RankThree.PartTwo.Sec21
