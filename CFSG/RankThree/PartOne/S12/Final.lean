module

public import CFSG.RankThree.PartOne.S12.Main
public import CFSG.RankThree.PartOne.S12.Sec12ThreeB
public import CFSG.RankThree.PartOne.S12.DischargeDickson
public import CFSG.RankThree.PartOne.LIT.KF126
public import CFSG.RankThree.PartOne.LIT.McLaughlin
public import CFSG.RankThree.PartOne.LIT.KFCGTList
public import CFSG.RankThree.PartOne.LIT.JonesParshall
public import CFSG.RankThree.PartOne.S12.Node126kFinal
public import CFSG.RankThree.PartOne.S13K.Refl136
public import CFSG.RankThree.PartOne.K156.Final
public import CFSG.CGT.PushingUpLit.CGT6.EightOneCore
public import CFSG.RankThree.PartOne.K1327.Final
public import CFSG.RankThree.PartOne.K1320X.CommRes
import CFSG.RankThree.PartOne.NF7J.PairOdd
public import CFSG.RankThree.PartOne.K133H.Heavy
import CFSG.RankThree.PartOne.Q1327Z.ReflAll
public import CFSG.RankThree.PartOne.U5E.Reinst
import CFSG.RankThree.PartOne.DISTX.Node136
import CFSG.RankThree.PartOne.DISTX.XneNodes
import CFSG.RankThree.PartOne.K1320X.Final
import CFSG.RankThree.PartOne.N143.Weyl613Final
import CFSG.RankThree.PartOne.AUTSL.MovedL4
import CFSG.RankThree.PartOne.HESS.Final
import CFSG.RankThree.PartOne.HNB.RowModelsDistinct
public import CFSG.RankThree.PartOne.S12.Sec1511EIRows
public import CFSG.RankThree.PartOne.KF.F128Plug
import CFSG.RankThree.PartOne.K1214.CycFinal
import CFSG.RankThree.PartOne.S12.Sec12FusGen
import CFSG.RankThree.PartOne.CTP.AsmWrap
import CFSG.RankThree.PartOne.CTP.StdMain
import CFSG.RankThree.PartOne.LSTD.Main
public import CFSG.RankThree.PartOne.N143.CaseSup
public import CFSG.RankThree.PartOne.N1322.Prim
public import CFSG.RankThree.PartOne.S12.Sec138I
public import CFSG.RankThree.PartOne.S12.Sec141Struct
public import CFSG.RankThree.PartOne.CTP.ExtB
public import CFSG.RankThree.PartOne.CTP.ExtPhan
public import CFSG.RankThree.PartOne.KF.BloomPrime
public import CFSG.RankThree.PartOne.KF.SU5Contained
public import CFSG.RankThree.PartOne.FIS.Item74
public import CFSG.RankThree.PartOne.S11b.Sec109Assembly
public import CFSG.RankThree.PartOne.S11b.Sec109Witness
public import CFSG.RankThree.PartOne.S11d.MixedCase
public import CFSG.RankThree.PartOne.S11d.ComponentExists
public import CFSG.RankThree.PartOne.S11d.BenderPCore
public import CFSG.RankThree.PartOne.S11d.MaximalExists
public import CFSG.RankThree.PartOne.S11d.InnerCase
public import CFSG.RankThree.PartOne.S11d.WeylThree
import CFSG.RankThree.PartOne.KLC.D4OutCentral
public import CFSG.RankThree.PartOne.S12.InspectionsOpen
public import CFSG.RankThree.PartOne.Q1327T.MCells

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.CGT.PushingUpLit (AschbacherNineContent AschbacherTheoremTwoK SolomonAlternatingBlockK)
open CFSG.CGT.PushingUpLit.CGT6 (AschbacherSixThreeCore pushingUpCorollaryΩ_of_core)

theorem vanishingRecognition_of_inputs (hSchreier : SchreierFor InCatalog)
    (hbridge : TauCetiCatalogBridge) (hr : SectionTenElevenOpen)
    (horth : OrthogonalOuterPrimeTwoTrivial) (hsporadic : SporadicOuterOrderLeTwoSimple)
    (h113 : Sec11Indeed.ThreeClaim) (h114 : Sec11Indeed.FourClaim)
    (hcore : Sec11Indeed.FiveClaimCore) (hfin : Sec11Indeed.FinalClaim)
    (hbranch : MaximalBranchThree)
    (hLS : FieldAutCoset) (htail : FieldCaseTail)
    (hKF122 : KF122) (hKF123 : KF123) (hNT : KF123NoTransvection)
    (hKF1 : KF128Rank1) (hKF2 : KF128Rk2c) (hBM : ExtBloomMitchell)
    (hGriess : CFSG.Open.GriessAllModelsStatement)
    (hLay : KF1212Layer) (hTyp : KF1213Type) (hRig : S12K.LieRigidity3) (hKR : K1214.KFixedRes)
    (hFrat : KF1214U5 → KF1215Frat) (hClass : KF1215Class)
    (hSp4 : InSec11Two → KF1214U5 → KF1215Sp4)
    (h133 : S13K.KF133Two)
    (hKty1322 : N1322.KF1322Kty) (hG21322 : N1322.KF1322G2)
    (hNF71322 : NF7H.KF1322NF7U) (hΩ1322 : N1322.KF1322OmegaList)
    (hN1322 : N1322.KF1322ThreeA6Norm)
    (hP5 : Q1327.KF1327P5) (hKB : Q1327T.KF1327BM) (hInsp : Q1327T.Row8U3Inspection)
    (hI613 : N143.Item613ListIdx) (hBridge : N143.EvenListBridge)
    (hSLB : N143.SectionListBound)
    (h1511 : Sec1511.KFEIMoved → Node154 → S15K.Sec13Avail → Node123 → KF156' → U5E.Reinst5 → Node1511)
    (h1514 : Sec1511.KFEIMoved → Node154 → S15K.Sec13Avail → Node123 → KF156' → U5E.Reinst5 → Node1514')
    (h154Five : KF154Five) (h15u5 : Sec1511.KFEIMoved → Node154 → S15K.Sec13Avail → Node123 → KF156' → U5E.Reinst5 → Node1515U5)
    (hFull106 : K156.Full106Stmt)
    (hCore : AschbacherSixThreeCore) (hN : AschbacherNineContent)
    (hTwoK : AschbacherTheoremTwoK) (hSolK : SolomonAlternatingBlockK) :
    VanishingRecognition := by
  have hB : ExtBloomPrime := extBloomPrime_of_mitchell hBM
  have hKFU4 : KF126U4 := kf126U4_of_multipliers hGriess
  have hI : SectionTenElevenInspections :=
    sectionTenElevenInspections_of_steps_simple hSchreier hbridge
      (hr.toRemaining hSchreier hGriess) horth hsporadic hKF1 h113 h114 hcore hfin
  obtain ⟨h107, h108, h105, h112, h11⟩ := sectionTenEleven_of_inspections hSchreier hbridge hI
  have h109 : InSec10Nine := Sec109.inSec10Nine_of_remaining_steps hSchreier h112
      Sec109.witnessExists (Sec109.componentExists_of hbridge hI.outInner benderPCore)
      (Sec109.maximalExists_of hSchreier hbranch) (Sec109.fieldCaseImpossible_of hLS htail)
      (Sec109.mixedCaseImpossible_of (fieldAutNormalizerPower KLC.d4OutCentral))
      (Sec109.innerCaseImpossible_of hSchreier h107 h108 hKF122 hKF123 innerWeylFact)
  have hsel := selected_prime_elements_normalize_theta_components
  have h106 := section_ten_maximal_moving_theta_components_quasisimple
  have h128 : Node128 := node128_of_split hSchreier twoActionInputs_of_S9 hsel h106 h112 hKF1 hKF2
  have hSU5 : InSU5Contained :=
    inSU5Contained_of_inputs hSchreier twoActionInputs_of_S9 hsel h106 h108
  have h122 : Node122 := node122_of_inputs hSchreier twoActionInputs_of_S9 hsel
    section_ten_maximal_component_quotient_actor_kernel_cyclic h106 h107 h108 hKF122 hSU5
  have h122b : Node122b := node122b_of_inputs hsel h122
  have h123 : Node123 :=
    node123_of_inputs hSchreier twoActionInputs_of_S9 h106 h107 h109 h122 hKF123
  have h124 : Node124 := node124_of_inputs h107 h109 h122 hKF123
  have h125 : Node125 := node125_of_inputs hSchreier twoActionInputs_of_S9 hsel h106 h107 h109
    section_ten_component_supplement_transitivity section_ten_trivial_actor_component_supplement
    section_ten_moving_two_stratum_upward_closure h105 h122 h124 h128 hNT
  have h124b : Node124b := node124b_of_inputs h107 h109 h122 hKF123
  have h126g : Node126g :=
    node126g_of_inputs h123 h124 h124b h125 laFaithful la126 extDickson hB extJonesParshall
      kf126
  have h126k : Node126k := node126k_of_inputs h122 h122b h123 h124 h124b h125 laFaithful la126
    extDickson hB extJonesParshall kf126 hKFU4 CTP.extPhan
  have h126 : Node126 := node126_of_parts h126g h126k
  have h127 : Node127 := node127_of_inputs h122b h123 h124 h125 h126 kf127
  have h1210 : Node1210 := node1210_of_inputs h122b h124 h124b h125
  have h1211 : Node1211 := node1211_of_inputs h124 h125 h1210
  have h1212 : Node1212a := node1212a_of_inputs h122b h123 h124 h1210
  have h1214U5 : KF1214U5 := CTP.kf1214U5_of_core hsel h112 hLS h124 (CTP.KF1212Layer.row12 hLay)
      (CTP.KF1213Type.row12 hTyp)
      (CTP.kf1214U5Core_of_frame
          (CTP.kf1214U5Frame_of_std hsel _ InSec10Seven InSec10Nine hGriess h107 h109 CTP.istd_holds
              (LSTD.lStd_of_inputs InSec10Seven InSec10Nine)))
  have hStr : KF1214Struct := K1214.kf1214Struct_holds h112 hRig hKR h1214U5
  have hfusRest : Node12FusionRest :=
    node12FusionRest_of_steps hLay (node1212Choice_of_inputs hsel) node1213Move_of_inputs
        node1213Max_of_inputs (node1213Two_of_inputs h124) (node1213Field_of_inputs h112 hLS) hTyp
        hStr h1214U5 node1214Syl_of_inputs (node1215Gen_of_inputs (hFrat h1214U5) hClass)
        (hSp4 h112 h1214U5)
  have hfus : Node12Fusion :=
    node12Fusion_of_rest hfusRest h122 h122b h123 h124 h125 h1210 h1211 h1212
  have hRe : S13K.Sec13Reinst := S13K.sec13Reinst_of_nodes hSchreier twoActionInputs_of_S9 h106 h11
    h122 h122b h123 h124 h125 h126 h127 h128 (node129_of_fusion hfus)
  have hOdd1322 : N1322.KF1322Odd :=
    K133B.kf1322Odd_of_heavy4 hGriess hSchreier hRe h133 hSLB hInsp K133H.row8OddHeavy4_holds
  have h1322 : Node1322 :=
    N1322.node1322_of_kfacts hBM hGriess (NF7J.pairMember_of_inputs hGriess hSchreier h133)
      hOdd1322 hKty1322 hG21322 hNF71322 hΩ1322 hN1322
  have hK1327 : K1327.KF1327Q :=
    Q1327Z.kf1327Q_of_inspection hGriess hSchreier hRe twoActionInputs_of_S9 hFull106 hSLB hI613
      hBridge hP5 hKB hInsp
  have hpair : KF134Pair := S13K.kf134Pair_of_core hGriess hSchreier hRe h133
  have hSame : S13K.KFCommSame := S13K.kfCommSame_of_core hGriess kf123Row1 h107 h109 h122
  have hAt : KF136At := S13K.KF136At_holds hGriess
  have hRefl : KF136Refl := S13K.kf136Refl_holds hGriess
  have hB2 : N143.Node143CommB2Sup := HESS.node143CommB2Sup_of_hess hGriess kf123Row1 h107 h109 h122 hpair
  have hHess : Node143Comm :=
    N143.node143Comm_of_list hGriess hSchreier h107 h109 h122 hpair hB2 hSLB
  have h136 : Node136 := DISTX.node136_of_members hGriess hSchreier hRe hSame kf123Row10 h107
    h109 h122 hRefl hAt
  have h137 : Node137 := node137_of_pair hpair h136 hSchreier twoActionInputs_of_S9 h106 h11 h122
    h122b h123 h124 h125 h126 h127 h128 (node129_of_fusion hfus)
  have h138I : Node138I := node138I_of_node137 (node137any_of_pair hpair h136 hSchreier
    twoActionInputs_of_S9 h106 h11 h122 h122b h123 h124 h125 h126 h127 h128
    (node129_of_fusion hfus))
  have hComm : KF134Comm :=
    DISTX.kf134Comm_of_members hSchreier hRe (S13K.kfLiftAll_holds hGriess) h133 hSame h136 h138I
      h124b
  have h138II : Node138II := node138II_of_loc (node138Loc_of_comm hKFU4 hComm) hpair h136 h138I
    hSchreier twoActionInputs_of_S9 h106 h11 h122 h122b h123 h124 h124b h125 h126 h127 h128
    (node129_of_fusion hfus)
  have h138T : Node138Trans :=
    node138Trans_of_nodes h136 h138I hSchreier twoActionInputs_of_S9 h106 h11 h122 h122b h123 h124
      h124b h125 h126 h127 h128 (node129_of_fusion hfus)
  have hXne : K1320X.KFCommDistinctXne :=
    DISTX.kfCommDistinctXne_of_nodes hSchreier hRe (S13K.kfLiftAll_holds hGriess) h133 hSame h136
      h138I h124b h137 h138T
  have hDist : S13K.KFCommDistinct :=
    K1320X.kfCommDistinct_of_ne hGriess hSchreier twoActionInputs_of_S9 hFull106 hXne
  have hU5T : K1320.KF1320UThreeAt 5 :=
    K1320X.kf1320UThreeAt_five_of_ne hGriess hSchreier twoActionInputs_of_S9 hFull106 h133 hXne
      HNB.rowModelsDistinct_holds
  have hU5 : KF1320U5 :=
    K1320.kf1320U5'_holds hGriess hSchreier h133 HNB.rowModelsDistinct_holds hU5T
  have hKF141 : KF141 :=
    S13K.kf141_of_core hGriess hSchreier hRe h133 hDist kf123Row1 h107 h109 h122
  have h138 : Node138 :=
    node138_of_struct (node138Struct_of_local FIS.inFischer44 h136 h138I h137 h138T h138II) hKFU4
      CTP.extPhan hSchreier twoActionInputs_of_S9 h106 h11 h122 h122b h123 h124 h125 h126 h127 h128
      (node129_of_fusion hfus)
  have hS1320 : Node1320Struct := node1320Struct_of_node1322 h123 h1322 hU5
  have hKSp : KF1320Sp := K1320.kf1320Sp'_holds hGriess hSchreier h133 hDist
  have hKU : KF1320U := K1320.kf1320U_holds hGriess hSchreier h133 hDist
    HNB.rowModelsDistinct_holds
  have hKL4 : KF1320L4 := K1327.kf1320L4'_holds_Q hGriess hSchreier hRe hDist twoActionInputs_of_S9 hFull106 hK1327
  have h1320 : Node1320 :=
    node1320_of_struct hS1320 hKSp hKU hKL4 CTP.extCurtisTitsCThreeSp CTP.extCurtisTitsBThree
      hSchreier twoActionInputs_of_S9 h106 h11 h122 h122b h123 h124 h125 h126 h127 h128
      (node129_of_fusion hfus)
  have h141S : Node141Struct := Sec141Struct.node141Struct_of_comm kf123Row1 h107 h109 h122 hpair
    hKF141 CTP.extCurtisTitsA hHess
  have h141 : Node141 :=
    node141_of_struct h141S hKF141 CTP.extCurtisTitsA hSchreier twoActionInputs_of_S9 h106 h11
      h122 h122b h123 h124 h125 h126 h127 h128 (node129_of_fusion hfus)
  have h154 : Node154 := Sec154.node154_of_nodes hSchreier twoActionInputs_of_S9 h106 h11 h122 h122b
    h123 h124 h125 h126 h127 h128 (node129_of_fusion hfus) h154Five
  have hS13 : S15K.Sec13Avail := S15K.sec13Avail_of_nodes hSchreier twoActionInputs_of_S9 h106 h11
    h122 h122b h123 h124 h125 h126 h127 h128 (node129_of_fusion hfus)
  have hKF156 : KF156' := K156.kf156'_of_full106 hGriess hSchreier twoActionInputs_of_S9 hFull106
    hS13 h1322 hS1320 h11 h122 h122b h123 h124 h125 h128
  have hR5 : U5E.Reinst5 := U5E.reinst5_of_nodes h11 h122 h122b h123 h124 h125
  have hL4EI : Sec1511.KFEIMovedL4 := AUTSL.kfEIMovedL4_holds hS1320 hGriess hSchreier hRe hDist
  have hMoved : Sec1511.KFEIMoved := Sec1511.kfEIMoved_of_inputs hS1320 hKSp hKU hL4EI h141S hKF141
    hSchreier twoActionInputs_of_S9 h106 h11 h122 h122b h123 h124 h125 h126 h127 h128
    (node129_of_fusion hfus)
  exact vanishingRecognition_of_nodes' h11 h126 h127 h128 hfus h138 h1320 h141
    (node1515'_of_items h122 h122b h123 h124 h125 (h1511 hMoved h154 hS13 h123 hKF156 hR5) (h1514 hMoved h154 hS13 h123 hKF156 hR5)
      (h15u5 hMoved h154 hS13 h123 hKF156 hR5))
    (pushingUpCorollaryΩ_of_core hCore hN hTwoK hSolK) kfCGTList

end CFSG.RankThree.PartOne
