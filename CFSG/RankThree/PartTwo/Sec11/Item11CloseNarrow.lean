module

public import CFSG.RankThree.PartTwo.Sec11.Item11CloseChain
public import CFSG.RankThree.PartTwo.Sec11.Item116R2Chain
public import CFSG.RankThree.PartTwo.Sec11.Item116R2ZElement
public import CFSG.RankThree.PartTwo.Sec11.Item116R2Fa
public import CFSG.RankThree.PartTwo.Sec11.Item116R2J3
public import CFSG.RankThree.PartTwo.Sec11.Item424FromD4
public import CFSG.RankThree.PartTwo.Sec11.Item1115BypassCube
public import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProof
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofCommL3
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res4ProofEnd
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res7ProofNotZ9
public import CFSG.RankThree.PartTwo.Sec11.Item1117ResProof
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res2Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1119Final
public import CFSG.RankThree.PartTwo.Sec11.Item1119ResProofSymS
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Centreless
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Final
public import CFSG.RankThree.PartTwo.Sec11.SimsR1Blackburn
public import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL2Rank
public import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL3Rank
public import CFSG.RankThree.PartTwo.Sec11.SimsR1L2CubeFaithful
public import CFSG.RankThree.PartTwo.Sec11.SimsR1L2CubeSolvable
public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38Holds
public import CFSG.RankThree.PartTwo.Sec11.SimsR1OddCentThree
public import CFSG.RankThree.PartTwo.Sec11.SimsR1OddTwoLocal
public import CFSG.RankThree.PartTwo.Sec11.SimsR1OddTwoStar
public import CFSG.RankThree.PartTwo.Sec9.Hyp91SmallBridge

public section

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

section Narrow116

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem component_center_eq_bot_of_sylow_narrow
    (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hFa : ThreeCentralCoverOmegaNonabelian') (hFb : SylowThreeNotRankTwoByCyclic)
    {C : Type} [Group C] [Finite C] (hC : SectionFourHyp C)
    (Rs : Sylow 3 (C ⧸ aschbacherSolvableCore 3 C))
    (hR : IsRankTwoByCyclic ↥(Rs : Subgroup (C ⧸ aschbacherSolvableCore 3 C)))
    (hcomm : ∀ x ∈ (Rs : Subgroup (C ⧸ aschbacherSolvableCore 3 C)),
      ∀ y ∈ (Rs : Subgroup (C ⧸ aschbacherSolvableCore 3 C)), x ^ 3 = 1 → y ^ 3 = 1 →
        x * y = y * x)
    {J : Subgroup (C ⧸ aschbacherSolvableCore 3 C)} (hJ : CFSG.IsComponent J) :
    Subgroup.center J = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ : aschbacherSolvableCore 3 (C ⧸ aschbacherSolvableCore 3 C) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec11.aschbacherSolvableCore_quotient_eq_bot C
  have hZ3 : IsPGroup 3 (Subgroup.center J) := isPGroup_center_component_of_theta hθ hJ
  have hdvd : 3 ∣ Nat.card (Subgroup.center J) := by
    obtain ⟨n, hn⟩ := hZ3.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      rw [← Subgroup.card_eq_one, hn, pow_zero]
    rw [hn]
    exact dvd_pow_self 3 hn0
  have hS4 : SectionFourHyp ↥J :=
    CFSG.RankThree.PartTwo.Sec4.Item462Proof.sectionFourHyp_component_of_largePrime h1 hC hJ
  rcases item4_3_split (Q := ↥J ⧸ Subgroup.center ↥J) (h43 ↥J hS4 hJ.1 hdvd) with hA | hB
  · obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rs hJ.2
    obtain ⟨x, hx, y, hy, hx3, hy3, hxy⟩ := hFa ↥J hJ.1 hZ3 hne (threeCoverModelA'_of_sectionFourHyp
      (CFSG.RankThree.PartTwo.Sec4.Item41Narrow.sectionFourHyp_quotient_center h1 h2 hS4 hJ.1) hA) P
    have hmem : ∀ z : ↥J, z ∈ (P : Subgroup ↥J) →
        (z : C ⧸ aschbacherSolvableCore 3 C) ∈ (Rs : Subgroup (C ⧸ aschbacherSolvableCore 3 C)) := by
      intro z hz
      have hz' : (z : C ⧸ aschbacherSolvableCore 3 C) ∈ (P : Subgroup ↥J).map J.subtype :=
        ⟨z, hz, rfl⟩
      rw [hP] at hz'
      exact (Subgroup.mem_inf.1 hz').1
    have hpow : ∀ z : ↥J, z ^ 3 = 1 → (z : C ⧸ aschbacherSolvableCore 3 C) ^ 3 = 1 := by
      intro z hz
      have h := congrArg Subtype.val hz
      simpa using h
    have hc := hcomm (x : C ⧸ aschbacherSolvableCore 3 C) (hmem x hx)
      (y : C ⧸ aschbacherSolvableCore 3 C) (hmem y hy) (hpow x hx3) (hpow y hy3)
    exact hxy (Subtype.ext (by simpa using hc))
  · obtain ⟨T⟩ : Nonempty (Sylow 3 (↥J ⧸ Subgroup.center ↥J)) := inferInstance
    exact hFb (↥J ⧸ Subgroup.center ↥J) hB T
      (rankTwoByCyclic_sylow_section Rs hR hJ.2 (QuotientGroup.mk' (Subgroup.center ↥J))
        (QuotientGroup.mk'_surjective _) T)

theorem censusDCentreless_core_narrow
    (h45 : Sec4.Item4_5) (h113 : Item113)
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h43 : Sec4.Item4_3) (hFa : ThreeCentralCoverOmegaNonabelian')
    (hFb : SylowThreeNotRankTwoByCyclic) : CensusDCentreless := by
  intro G _ _ A c L a R Y d h hT _ _ J hJ
  have hG : TheoremFourHyp G := h.toSec11StdLocal.toHyp81.toPartTwoStanding.toTheoremFourHyp
  have hcd1 : c * d ≠ 1 := by
    intro h1
    apply h.not_mem_zpowers
    have hd' : d = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hd']
    exact inv_mem (Subgroup.mem_zpowers c)
  have hCtop : Subgroup.centralizer ({c * d} : Set G) ≠ ⊤ :=
    CFSG.RankThree.PartTwo.Sec6.centralizer_ne_top_of_ne_one hG hcd1
  have hC : SectionFourHyp (CAt (c * d)) := hG.sectionFourHyp hCtop
  obtain ⟨Rs, hR, hcomm⟩ := cd_Rbar_shape h45 h113 h hT
  exact component_center_eq_bot_of_sylow_narrow h1 h2 h43 hFa hFb hC Rs hR hcomm hJ

theorem twoStarAtCD_of_finite_facts_narrow
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore) (hP2c : Item116P2c)
    (hZ : ZElement) (hK2 : KFacts.KPSz) (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hFa : ThreeCentralCoverOmegaNonabelian') (hFb : SylowThreeNotRankTwoByCyclic) :
    ResidueR1TwoStarCD :=
  twoStarAtCD_of_inputs_k1 h45 h113 hcore hP2c hZ hK2
    (censusDCentreless_core_narrow h45 h113 h1 h2 h43 hFa hFb)

theorem residueTR1_of_cd_finite_facts_narrow
    (hB : KFacts.BlackburnRankTwo)
    (hFC : FactFieldCentralizerL2Odd) (hFC3 : FactFieldCentralizerL3)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore) (hP2c : Item116P2c)
    (hZ : ZElement) (hK2 : KFacts.KPSz) (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hFa : ThreeCentralCoverOmegaNonabelian') (hFb : SylowThreeNotRankTwoByCyclic)
    (hC38 : ResidueR1TwoStarCL38) (hCodd : ResidueR1TwoStarCOdd) : ResidueTR1 :=
  residueTR1_of_core' hB hFC hFC3 h45 h113 hcore hP2c
    (twoStarAtCD_of_finite_facts_narrow h45 h113 hcore hP2c hZ hK2 h1 h2 h43 hFa hFb) hC38 hCodd

theorem residueTR1_of_cd_remaining_narrow
    (h113 : Item113) (hZ : ZElement) (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hFa : ThreeCentralCoverOmegaNonabelian') (hFb : SylowThreeNotRankTwoByCyclic) :
    ResidueTR1 :=
  residueTR1_of_cd_finite_facts_narrow SimsR1.Blackburn.blackburnRankTwo_holds
    SimsR1.FieldCent.factFieldCentralizerL2Odd_holds SimsR1.FieldCent.factFieldCentralizerL3_holds
    Sec4.rank3II_4_5 h113 item116P2bCore_holds
    (item116P2c_of (item116P2b_of_core Sec4.rank3II_4_5 item116P2bCore_holds) Sec4.rank3II_4_5
      (Sec4.rank3II_4_8_of Sec4.rank3II_4_5))
    hZ KFacts.kpSz h1 h2 h43 hFa hFb residueR1TwoStarCL38_holds (residueR1TwoStarCOdd_of
        SimsR1.Blackburn.blackburnRankTwo_holds SimsR1.l2CubeTwoLocal_holds
        SimsR1.l2CubeFaithfulFix_holds
        (SimsR1.l2CubeSolvableFix_of_faithful SimsR1.l2CubeFaithfulFix_holds)
        SimsR1.l2CubeCentThree_holds Sec4.rank3II_4_5)

theorem residueTR1_of_cd_zElement_narrow
    (h113 : Item113) (hZ : ZElement)
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) :
    ResidueTR1 :=
  residueTR1_of_cd_remaining_narrow h113 hZ h1 h2 h43 threeCentralCoverOmegaNonabelian'_holds
    (sylowThreeNotRankTwoByCyclic_of_J3 sylowThreeNotRankTwoByCyclicJ3_holds)

theorem residueTR1_of_cd_narrow
    (h113 : Item113) (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) : ResidueTR1 :=
  residueTR1_of_cd_zElement_narrow h113 zElement_holds h1 h2 h43

theorem item116_of_standing_narrow
    (h97 : Sec9.Item97) (h98 : Sec9.Item98) (h113 : Item113)
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) :
    Item116 :=
  item116_of h97 h98 Sec4.rank3II_4_5 (Sec4.rank3II_4_8_of Sec4.rank3II_4_5)
    (item116Fusion_of_residueTR1 (residueTR1_of_cd_narrow h113 h1 h2 h43) item116P2bCore_holds
      Sec4.rank3II_4_5 h113
      (item116P2c_of (item116P2b_of_core Sec4.rank3II_4_5 item116P2bCore_holds) Sec4.rank3II_4_5
        (Sec4.rank3II_4_8_of Sec4.rank3II_4_5)))

end Narrow116

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Close

theorem narrow_sec11Item116
    : Sec11.Item116 :=
  Sec11.item116_of_standing_narrow closed_sec9Item97 closed_sec9Item98 closed_sec11Item113
    closed_sec4Item4_1LargePrime closed_sec4Item4_1ThreeCover closed_sec4Item4_3

theorem narrow_sec11Item117
    : Sec11.Item117 :=
  Sec11.item117_of_item97 closed_sec9Item97 closed_sec11Item112 closed_sec11Item113
    narrow_sec11Item116

theorem narrow_sec11Item118
    : Sec11.Item118 :=
  Sec11.item118_of narrow_sec11Item117 closed_sec4Item4_5 closed_sec4Item4_8

theorem narrow_sec11Item119
    : Sec11.Item119 :=
  Sec11.item119_of_items closed_sec11Item112 closed_sec11Item114 narrow_sec11Item117
    narrow_sec11Item118

theorem narrow_sec11Item1116
    : Sec11.Item1116 :=
  Sec11.item1116_of_item82 closed_sec4Item4_5 closed_sec11Item113 narrow_sec11Item117
    closed_sec8Item82One narrow_sec11Item118 narrow_sec11Item119 closed_sec11CentBound119

theorem narrow_sec11Item1117
    : Sec11.Item1117 :=
  Sec11.item1117_of_res7' closed_sec4Item4_5 closed_sec4Item4_8 closed_sec9Item97
    closed_sec11Item113 narrow_sec11Item117 narrow_sec11Item118 narrow_sec11Item119
    closed_sec8Item82One closed_sec10Item1016 narrow_sec11Item1116 closed_sec11KFact1117CubeG2
    closed_sec11KFact1117CubeL3 closed_sec11AutThree1129

theorem narrow_sec11Item11131
    : Sec11.Item11131 :=
  Sec11.item11131_of_item82 closed_sec8Item82One narrow_sec11Item118 closed_sec4Item4_5

theorem narrow_sec11Item11133Field
    : Sec11.Item11133Field :=
  Sec11.item11133Field_of_item82 closed_sec4Item4_5 closed_sec4Item4_8 closed_sec8Item82One
    narrow_sec11Item118

theorem narrow_sec11KFact1118InvElt
    : Sec11.KFact1118InvElt :=
  Sec11.kFact1118InvElt_of_basic closed_sec4Item4_5 narrow_sec11Item117

theorem narrow_sec11SetUp1118
    : Sec11.SetUp1118 :=
  Sec11.setUp1118_of_res5_invElt closed_sec4Item4_5 closed_sec4Item4_6 closed_sec11Item113
    narrow_sec11Item117 narrow_sec11Item119 narrow_sec11Item11131
    narrow_sec11Item11133Field narrow_sec11Item1117 closed_sec11KFact1118Triality46
    narrow_sec11KFact1118InvElt

theorem narrow_sec11Step1119CommG2
    : Sec11.Step1119CommG2 :=
  Sec11.step1119CommG2_of_model closed_sec4Item4_5 narrow_sec11Item117

theorem narrow_sec11Step1119CommD4
    : Sec11.Step1119CommD4 :=
  Sec11.step1119CommD4_of_basic closed_sec4Item4_5 narrow_sec11Item117

theorem narrow_sec11Step1119CommL3
    : Sec11.Step1119CommL3 :=
  Sec11.step1119CommL3_holds narrow_sec11Item117

theorem narrow_sec11Step1119Comm
    : Sec11.Step1119Comm :=
  Sec11.step1119Comm_of narrow_sec11Step1119CommG2 narrow_sec11Step1119CommD4
    narrow_sec11Step1119CommL3

theorem narrow_sec11Step1119SymS
    : Sec11.Step1119SymS :=
  Sec11.step1119SymS_of closed_sec4Item4_5 closed_sec4Item4_8 closed_sec11Item113
    narrow_sec11Item117

theorem narrow_sec11Step1119SymTypes
    : Sec11.Step1119SymTypes :=
  Sec11.step1119SymTypes_of_standing_final closed_sec11Item113 narrow_sec11Item117
    narrow_sec11Item118 narrow_sec11Item119

theorem narrow_sec11Step1119SymC
    : Sec11.Step1119SymC :=
  Sec11.step1119SymC_of_types closed_sec4Item4_5 closed_sec4Item4_8 closed_sec9Item97
    closed_sec11Item113 narrow_sec11Item117 narrow_sec11Item119 closed_sec10Item1016
    narrow_sec11Item1116 narrow_sec11Item1117 narrow_sec11Step1119SymTypes

theorem narrow_sec11Step1119Sym
    : Sec11.Step1119Sym :=
  Sec11.step1119Sym_of narrow_sec11Item1117 narrow_sec11Step1119SymS
    narrow_sec11Step1119SymC

theorem narrow_sec11Item1119
    : Sec11.Item1119 :=
  Sec11.item1119_of closed_sec4Item4_5 closed_sec11Item113 narrow_sec11Item117
    narrow_sec11Step1119Comm narrow_sec11Step1119Sym

theorem narrow_sec11Item1120
    : Sec11.Item1120 :=
  Sec11.item1120_of_standing_no118 closed_sec11Item113 narrow_sec11Item117 narrow_sec11Item119

theorem narrow_sec11Sec11BigNever
    : Sec11.Sec11BigNever :=
  Sec11.sec11BigNever_of_res4 closed_sec4Item4_5 closed_sec4Item4_8 closed_sec11Item113
    narrow_sec11Item117 narrow_sec11Item1119 narrow_sec11Item1120
    closed_sec11KFact1121Lists

theorem narrow_sec11Item1118
    : Sec11.Item1118 :=
  Sec11.item1118_of narrow_sec11Item1116 narrow_sec11Item1117 narrow_sec11SetUp1118
    narrow_sec11Sec11BigNever

theorem narrow_sec11Item1115
    : Sec11.Item1115 :=
  Sec11.item1115_of_mhoV closed_sec4Item4_5 closed_sec11Item113 narrow_sec11Item117

theorem narrow_sec11Item1121N
    : Sec11.Item1121N :=
  Sec11.item1121N_of closed_sec4Item4_5 closed_sec4Item4_8 closed_sec11Item113 narrow_sec11Item117 narrow_sec11Item1115 narrow_sec11Item1120 closed_sec11KFact1121Lists

theorem narrow_sec11Inverter1118
    : Sec11.Inverter1118 :=
  Sec11.inverter1118_of_res4 closed_sec4Item4_5 closed_sec4Item4_8 closed_sec11Item113
    narrow_sec11Item117 narrow_sec11Item1119 narrow_sec11Item1120
    closed_sec11KFact1121Lists

theorem narrow_sec11Item1123
    : Sec11.Item1123 :=
  Sec11.item1123_of closed_sec4Item4_5 closed_sec11Item113 narrow_sec11Item117
    narrow_sec11Item1117 narrow_sec11Item1119 narrow_sec11Item1120
    narrow_sec11Item1121N narrow_sec11Inverter1118

theorem narrow_sec11Item119Used
    : Sec11.Item119Used :=
  Sec11.item119Used_of_item119 narrow_sec11Item119

theorem narrow_sec11Sylow1129
    : Sec11.Sylow1129 :=
  Sec11.sylow1129_of_res7' closed_sec4Item4_5 closed_sec11Item113 narrow_sec11Item117
    narrow_sec11Item118 narrow_sec11Item119Used closed_sec11AutThree1129

theorem narrow_sec11Final1128
    : Sec11.Final1128 :=
  Sec11.final1128_of narrow_sec11Item117 narrow_sec11Sylow1129

theorem narrow_sec11Choose1128
    : Sec11.Choose1128 :=
  Sec11.choose1128_of_final1128 narrow_sec11Final1128

theorem narrow_sec11Item1128
    : Sec11.Item1128 :=
  Sec11.item1128_of closed_sec4Item4_5 narrow_sec11Item1116 narrow_sec11Item1117
    narrow_sec11Item1118 narrow_sec11Choose1128

theorem narrow_sec11Item1132
    : Sec11.Item1132 :=
  Sec11.item1132_of_res7' closed_sec4Item4_5 closed_sec11Item113 narrow_sec11Item117
    narrow_sec11Item118 narrow_sec11Item119Used closed_sec11AutThree1129

theorem narrow_sec11Sec11DataExists
    : Sec11.Sec11DataExists :=
  Sec11.sec11DataExists_of closed_sec9Item97 closed_sec4Item4_5 closed_sec11Item113
    narrow_sec11Item117 narrow_sec11Item119

theorem narrow_sec11Item1134E27
    : Sec11.Item1134E27 :=
  Sec11.item1134E27_of_steps_final1128 closed_sec10Item1016 closed_sec9Item97 closed_sec4Item4_5
    closed_sec4Item4_8 closed_sec11Item113 narrow_sec11Item117 narrow_sec11Sec11DataExists
    narrow_sec11Item1116 narrow_sec11Item1117 narrow_sec11SetUp1118
    narrow_sec11Item1119 narrow_sec11Item1123 narrow_sec11Inverter1118
    narrow_sec11Final1128

theorem narrow_sec11Sec11Never
    : Sec11.Sec11Never :=
  Sec11.sec11Never_of narrow_sec11Sec11DataExists narrow_sec11Item1128
    narrow_sec11Item1132 closed_sec11Item1133

theorem narrow_sec11Hyp91Never
    : Sec11.Hyp91Never :=
  Sec11.hyp91Never_of_item1016 closed_sec10Item1016 closed_sec11SetUp11 narrow_sec11Sec11Never

theorem narrow_sec9Hyp91SmallNever
    : Sec9.Hyp91SmallNever :=
  Sec9.hyp91SmallNever_of_hyp91Never narrow_sec11Hyp91Never

theorem narrow_sec11Item1134E27N
    : Sec11.Item1134E27N :=
  Sec11.item1134E27N_of narrow_sec9Hyp91SmallNever

end Close

theorem item1134E27_of_standing_narrow
    : Item1134E27 :=
  Close.narrow_sec11Item1134E27

theorem item1134E27N_of_standing_narrow
    : Item1134E27N :=
  Close.narrow_sec11Item1134E27N

end Certified

end CFSG.RankThree.PartTwo.Sec11
