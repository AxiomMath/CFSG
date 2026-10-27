module

public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofTheta419Assembly
public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofGammaU
public import CFSG.RankThree.PartTwo.Sec8.Item84PairProof86
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofRee
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item86ResProof

theorem pair84PartnerU_of_gamma (h45 : Sec4.Item4_5) (h418 : Item418Theta)
    (hUL : Pair84GammaUL) (hNL : Pair84GammaNL) (hRee : Pair84GammaRee) : Pair84PartnerU :=
  have hR : KF84FieldReeStd := kF84FieldReeStd_holds
  have hO : KF84OuterL2 :=
    kF84OuterL2_of (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
  have hF : KF84FieldStd := kF84FieldStd_of hO hR
  pair84PartnerU_of h418 (kF83KBarTwo_of_even (kF83KBarEven_of hO hR))
    (kF83Indep_of kF83IndepGTwo_holds) hF (Item84Pair.pair84GammaU_of h45 h418 hF)
    (pair84GammaNonempty_of hUL hNL hRee)

theorem item812_of_res14 (h83 : Item83) (h83a : Item83After) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hN : Pair84GammaNonempty)
    (h1 : Pair86One) (h87 : Item87) (h88 : Item88) (h84 : Pair84A)
    (h419 : Sec4.Item4_19ThetaJ3) (hJ3 : KF89NotJ3) (hcomp : KF89JCompNe)
    (h611 : Sec6.Item6_11_1) (hMinus : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus)
    (hFix : KF89D4FixInv) (hU38 : KF89BNotCentIU38) (hOF : KF89OmegaFixInvNonSp)
    (hbY : Fin812BMemY) (hQ1 : Fin812Q1Cyclic) : Item812 :=
  have hR : KF84FieldReeStd := kF84FieldReeStd_holds
  have hO : KF84OuterL2 :=
    kF84OuterL2_of (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
  have hF : KF84FieldStd := kF84FieldStd_of hO hR
  have hKB : Item83Proof.KF83KBarTwo := kF83KBarTwo_of_even (kF83KBarEven_of hO hR)
  have hU : Pair84GammaU := Item84Pair.pair84GammaU_of h45 h418 hF
  have h84U : Pair84PartnerU :=
    pair84PartnerU_of h418 hKB (kF83Indep_of kF83IndepGTwo_holds) hF hU hN
  item812_of_res13 h83 h83a h45 h48 h418 hU hN h1 h87 h88 h84 h419 hJ3 hcomp h611 h84U hMinus
    hFix hU38 hOF hbY hQ1

theorem item812_of_res15 (h83 : Item83) (h83a : Item83After) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hUL : Pair84GammaUL) (hNL : Pair84GammaNL)
    (hRee : Pair84GammaRee) (hT : Pair86NonUnitary) (h87 : Item87) (h88 : Item88)
    (h84 : Pair84A)
    (h419 : Sec4.Item4_19ThetaJ3) (hJ3 : KF89NotJ3) (hcomp : KF89JCompNe)
    (h611 : Sec6.Item6_11_1) (hMinus : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus)
    (hFix : KF89D4FixInv) (hU38 : KF89BNotCentIU38) (hOF : KF89OmegaFixInvNonSp)
    (hbY : Fin812BMemY) (hQ1 : Fin812Q1Cyclic) : Item812 :=
  item812_of_res14 h83 h83a h45 h48 h418 (pair84GammaNonempty_of hUL hNL hRee)
    (pair86One_of hT hUL) h87 h88 h84 h419 hJ3 hcomp h611 hMinus hFix hU38 hOF hbY hQ1

end CFSG.RankThree.PartTwo.Sec8
