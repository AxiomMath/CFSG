module

public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofG2E9
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofD4
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item86ResProof

theorem pair84GammaNL_of' (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hL : Item82TwoList) :
    Pair84GammaNL :=
  Item8KFacts3.pair84GammaNL_of h45 h418 hL Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds
    Sec11.KS11Lie7Proof.g2ThreeACentMinus_holds kF84Sp4ThreeCent_holds

theorem pair84GammaRee_of' (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hL : Item82TwoList)
    (hStd : KF84D4OuterSU3Std) : Pair84GammaRee :=
  Item8KFacts3.pair84GammaRee_of h45 h418 hL Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds
    kF84G2E9_holds (kF84D4OuterSU3_of hStd) kF84Sp4ThreeCent_holds

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4
