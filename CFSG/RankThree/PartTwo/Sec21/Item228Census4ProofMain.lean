module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofTits
public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofUni
public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofPSL
public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofExc
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofSpor
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofA9
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSp62
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofU3
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofExc
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofSp4
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofU4
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofUni
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec21

section L3Type


theorem census228L3Type_holds : Census228L3Type :=
  census228L3Type_of census228L3TypeLinOdd_holds census228L3TypeUniOdd_holds
    census228L3TypeUniTwo_holds census228L3TypeSLEven_holds census228L3TypePSLEven_holds

theorem census228ChevTwoRest_holds :
    Census228ChevTwoRest :=
  census228ChevTwoRest_of census228Sp4Two_holds census228U4Two_holds
    Sec8.ReeF4Conj2Proof.census228Ree2F4_holds census228Tits_holds

theorem census228ExcStar_of_aut
    (h : Census228ExcTwoEvenAut) : Census228ExcStar :=
  census228ExcStar_of census228G2TwoOdd_holds census228D4TwoOdd_holds (census228ExcTwoEven_of h)

end L3Type

section Census


theorem inspection228ListMono_of_census4 (hHigh : Outer223High) (hG2 : Census228G2Odd)
    (hSp : Census228PSp4Odd) (hU4 : Census228U4Odd) (hL4 : Census228L4Odd)
    (hSpor : Census228SporData) (hExc : Census228ExcTwoEvenAut) (hSp62 : Census228Sp62Data) :
    Inspection228ListMono :=
  inspection228ListMono_of_split hHigh census228L3Type_holds
    (census228Inner_of_families census228L3Rest_holds (census228LieOdd_of hG2 hSp hU4 hL4)
      (census228Alt_of census228AltNine_holds) (census228Spor_of (census228SporRest_of hSpor))
      census228SporStar_holds census228ChevTwoRest_holds (census228ExcStar_of_aut hExc)
      (census228Sp62_of hSp62) (census228CharThree_of census228CharThreeLin_holds))

end Census

end CFSG.RankThree.PartTwo.Sec21
