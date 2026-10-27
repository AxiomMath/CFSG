module

public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofU38
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofE27
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofD4
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofRee
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofU
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairRee
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item86ResProof

theorem kF89OmegaFixInvNonSp_of_h45 (h45 : Sec4.Item4_5) : KF89OmegaFixInvNonSp :=
  kF89OmegaFixInvNonSp_of_ree h45 Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds
    kF89D4FixInv_holds kF89D4FixInvEven_holds kF89ReeFixInv_holds (kF89OmegaFixInvUnitary_of h45)

theorem fin812BMemY_of_unitary (h84 : Pair84A) (hbYU : Fin812BMemYU) : Fin812BMemY :=
  fin812BMemY_of h84 kF812E27PerfCent_holds hbYU

theorem item812_of_res17 (h83 : Item83) (h83a : Item83After) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hUL : Pair84GammaUL) (hNL : Pair84GammaNL)
    (hRee : Pair84GammaRee) (hT : Pair86NonUnitary) (h87 : Item87) (h88 : Item88)
    (h84 : Pair84A) (h419 : Sec4.Item4_19ThetaJ3) (hJ3 : KF89NotJ3) (hcomp : KF89JCompNe)
    (h611 : Sec6.Item6_11_1) (hbYU : Fin812BMemYU) (hQ1 : Fin812Q1Cyclic) : Item812 :=
  item812_of_res15 h83 h83a h45 h48 h418 hUL hNL hRee hT h87 h88 h84 h419 hJ3 hcomp h611
    Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds kF89D4FixInv_holds (kF89BNotCentIU38_of h45)
    (kF89OmegaFixInvNonSp_of_h45 h45) (fin812BMemY_of_unitary h84 hbYU) hQ1

theorem item812_of_res18 (h83 : Item83) (h83a : Item83After) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hUL : Pair84GammaUL) (hL : Item82TwoList)
    (hSp : Item8KFacts3.KF84Sp4ThreeCent) (hE9 : Item8KFacts3.KF84G2E9)
    (hD4 : Item8KFacts3.KF84D4OuterSU3) (hT : Pair86NonUnitary) (h87 : Item87) (h88 : Item88)
    (h84 : Pair84A) (h419 : Sec4.Item4_19ThetaJ3) (hJ3 : KF89NotJ3) (hcomp : KF89JCompNe)
    (h611 : Sec6.Item6_11_1) (hbYU : Fin812BMemYU) (hQ1 : Fin812Q1Cyclic) : Item812 :=
  item812_of_res17 h83 h83a h45 h48 h418 hUL
    (Item8KFacts3.pair84GammaNL_of h45 h418 hL Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds
      Sec11.KS11Lie7Proof.g2ThreeACentMinus_holds hSp)
    (Item8KFacts3.pair84GammaRee_of h45 h418 hL Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds
      hE9 hD4 hSp)
    hT h87 h88 h84 h419 hJ3 hcomp h611 hbYU hQ1

end CFSG.RankThree.PartTwo.Sec8
