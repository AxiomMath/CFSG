module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaD4
public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofG2Two
public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaCent
public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofQ2
public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofBEq
public import CFSG.RankThree.PartTwo.Sec8.Item812Res9ProofG2Two
public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofTheta419
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofRee
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even
import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofPGL3
import CFSG.RankThree.PartTwo.Sec8.Item812Res9ProofRee
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofPaExp
public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofBWeak

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item86ResProof

theorem sec8Never_of_kF89J (h45 : Sec4.Item4_5) (h87 : Item87) (h88 : Item88) (h84 : Pair84A)
    (hJ : KF89J) (hD4 : KF89D4OtherClass) (h83 : Item83) (hOC : Pair89OmegaCent)
    (hGI : Pair89GammaInner) (hOD : Pair89OmegaD4) (h84U : Pair84PartnerU)
    (h85 : Pair85Exists) (h86 : Pair86Exists) (hKB : Item83Proof.KF83KBarTwo)
    (hG2 : KF83IndepGTwo) (hBq : Fin812BEq) (hQR : Fin812QR) (hGN : Pair86GTwoN) :
    Sec8Never :=
  have hXY := item89XY_of_d4 h88 h84 hJ hD4
  have hsym := pair84Sym_of_xy h45 h87 hXY
  sec8Never_of_xy h87 h88 h84 hsym hXY
    (pair89InConfig_of_xy (pair89Occurs_of_narrowU_item45 (pair89OmegaStd_of h83 hOC hGI hOD) h45
      h84U h85 h86 hKB hG2 hGN) h87 hXY hsym h84)
    (fin812Sylow_of_res5 (fin812PaExp_of_84 h84) hBq hQR
      (fin812BWeak_of h84 hBq hQR kF812WreathCent_holds))

theorem item812_of_kF89J (h83 : Item83) (h83a : Item83After) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hO : KF84OuterL2) (hR : KF84FieldReeStd)
    (hGT : KF83GTwoTwo) (hU : Pair84GammaU) (hN : Pair84GammaNonempty) (h1 : Pair86One)
    (hS : KF86D4ShiftConj) (h87 : Item87) (h88 : Item88) (h84 : Pair84A) (hJ : KF89J)
    (hD4 : KF89D4OtherClass) (hOC : Pair89OmegaCent) (hGI : Pair89GammaInner)
    (hOD : Pair89OmegaD4) (h84U : Pair84PartnerU) (h85 : Pair85Exists)
    (hKB : Item83Proof.KF83KBarTwo) (hG2 : KF83IndepGTwo) (hBq : Fin812BEq) (hQR : Fin812QR) :
    Item812 :=
  Item83Proof.item812_of_choice86Var h83 h83a
    (choice86Var_of_res7 h45 h48 h418 hO hR hGT hU hN h1 hS)
    (sec8Never_of_kF89J h45 h87 h88 h84 hJ hD4 h83 hOC hGI hOD h84U h85
      (pair86Exists_of h418 (kF84FieldStd_of hO hR) h1 (pair86D4_of h45 h418 hO hR hS)) hKB hG2
      hBq hQR (pair86GTwoN_of_res7 h45 h418 hO hR hS))

theorem item812_of_res13 (h83 : Item83) (h83a : Item83After) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hU : Pair84GammaU) (hN : Pair84GammaNonempty)
    (h1 : Pair86One) (h87 : Item87) (h88 : Item88) (h84 : Pair84A)
    (h419 : Sec4.Item4_19ThetaJ3) (hJ3 : KF89NotJ3) (hcomp : KF89JCompNe)
    (h611 : Sec6.Item6_11_1) (h84U : Pair84PartnerU)
    (hMinus : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus) (hFix : KF89D4FixInv)
    (hU38 : KF89BNotCentIU38) (hOF : KF89OmegaFixInvNonSp) (hbY : Fin812BMemY)
    (hQ1 : Fin812Q1Cyclic) : Item812 :=
  have hR : KF84FieldReeStd := kF84FieldReeStd_holds
  have hO : KF84OuterL2 :=
    kF84OuterL2_of (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
  have hGI2 : KF83IndepGTwo := kF83IndepGTwo_holds
  have hKB : Item83Proof.KF83KBarTwo := kF83KBarTwo_of_even (kF83KBarEven_of hO hR)
  have h85 : Pair85Exists := pair85Exists_of h45 h48 hKB (kF83Indep_of hGI2) hO hR
  have hEv : KF89D4SecondCentEven := kF89D4SecondCentEven_of_y0 kF89D4SecondCentY0Even_holds
  have hG2o : KFG2Ord3Inv := kFG2Ord3Inv_of hMinus kFG2Ord3InvTwo_holds
  have hS : KF86D4ShiftConj :=
    kF86D4ShiftConj_of hG2o LangTwisted3Proof.kFPGL3Ord3Classes_holds hEv
  have hJ2 : KF89JTwoLocal :=
    kF89JTwoLocal_of h84 (kF89G2TwoLocal_of hG2o kF89G2TwoTwoLocal_holds) kF89Sp4TwoLocal_holds
      kF89ReeTwoLocal_holds
  have hBI : KF89BNotCentI :=
    kF89BNotCentI_of h45 (kF89BNotCentIUnitary_of h45 hU38) kF89ReeTwoLocal_holds
  have hJ : KF89J := kF89J_of_theta_ne h419 hJ3 (kF89JCentA_of h45 h84 hJ2 hBI) hcomp h84 h611
  item812_of_kF89J h83 h83a h45 h48 h418 hO hR kF83GTwoTwo_holds hU hN h1 hS h87 h88 h84 hJ
    kF89D4OtherClass_holds (pair89OmegaCent_of h45 hOF) (pair89GammaInner_of h45 hEv)
    (pair89OmegaD4_of h45 hS hFix) h84U h85 hKB hGI2 (fin812BEq_of_memY h84 hbY)
    (fin812QR_of_res10' h45 h84 hQ1)

end CFSG.RankThree.PartTwo.Sec8
