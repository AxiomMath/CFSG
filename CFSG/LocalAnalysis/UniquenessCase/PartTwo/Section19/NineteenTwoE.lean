module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFourFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CentSectionConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.Quasithin.H13.L32AC47h
public import CFSG.GroupTheory.SylowSupCentralizer
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K31
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelQuotientA5U34
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement
open scoped Classical

variable {G : Type} [Group G] [Finite G]

theorem sylow_three_le_sup_centOverO2 {D : Data G} (h642 : P17_64_2 D 5 2)
    (hK : K_A5U34BorelQuotient) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M) :
    S ≤ S17.Lp D 5 ⊔ F08.CentOverO2 D.M (S17.Lp D 5) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Subgroup G := S17.Lp D 5
  have hYM : Y ≤ D.M := S17.Lp_le_M D 5
  have hN : D.M ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hYM]
    exact s13_Lp_normal D.M 5
  let ρ : ↥D.M →* MulAut (Bar2 Y) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL Y).comp (Subgroup.inclusion hN)
  have hshape : IsL2Square (Bar2 Y) 2 ∨ IsL2U3Product (Bar2 Y) 2 :=
    Or.imp And.left And.left h642
  have hOut2 : IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 Y)) :=
    (hK (Bar2 Y) 2 rfl hshape).1
  have hinner : ∀ sS : ↥(S.subgroupOf D.M),
      ρ ⟨(sS : G), hS.le (Subgroup.mem_subgroupOf.mp sS.2)⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 Y) := by
    intro sS
    let sM : ↥D.M := ⟨(sS : G), hS.le (Subgroup.mem_subgroupOf.mp sS.2)⟩
    have hodd : Odd (orderOf (ρ sM)) := by
      obtain ⟨k, hk⟩ := hS.isPGroup.exists_card_eq
      have hdvd2 : orderOf sM ∣ Nat.card ↥S := by
        rw [← Subgroup.orderOf_coe sM]
        exact Subgroup.orderOf_dvd_natCard S (by
          have h := (Subgroup.mem_subgroupOf.mp sS.2 : (sS : G) ∈ S)
          simpa using h)
      have hdvd : orderOf (ρ sM) ∣ Nat.card ↥S := (orderOf_map_dvd ρ sM).trans hdvd2
      rw [hk] at hdvd
      exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) hdvd
    have hmem := CFSG.Quasithin.H13.L32A.C.mem_inner_of_odd_orderOf hOut2 hodd
    change ρ sM ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 Y) at hmem
    exact hmem
  intro s hsS
  let sM : ↥D.M := ⟨s, hS.le hsS⟩
  let sS : ↥(S.subgroupOf D.M) := ⟨sM, hsS⟩
  have hsM : s ∈ D.M := sM.2
  obtain ⟨ybar, hybar⟩ := hinner sS
  obtain ⟨y0, hy0⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) ybar
  have hy0Y : (y0 : G) ∈ Y := y0.2
  have hρy : ρ ⟨(y0 : G), hYM hy0Y⟩ = MulAut.conj ybar := by
    have hρy' : ρ ⟨(y0 : G), hYM hy0Y⟩ =
        MulAut.conj (QuotientGroup.mk (⟨(y0 : G), hy0Y⟩ : ↥Y)) := by
      change (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL Y)
        (Subgroup.inclusion hN ⟨(y0 : G), hYM hy0Y⟩) = _
      ext z
      induction z using QuotientGroup.induction_on with
      | H z =>
        rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk, MulAut.conj_apply]
        have hrep : ((Y.normalizerMonoidHom
            (Subgroup.inclusion hN ⟨(y0 : G), hYM hy0Y⟩)) z : ↥Y) =
            (⟨(y0 : G), hy0Y⟩ * z * ⟨(y0 : G), hy0Y⟩⁻¹ : ↥Y) := by
          apply Subtype.ext
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
          rfl
        rw [hrep]
        rfl
    rw [hρy']
    simpa using congrArg MulAut.conj hy0
  have hkey : ρ (⟨(y0 : G), hYM hy0Y⟩⁻¹ * sM) = 1 := by
    rw [map_mul, map_inv, hρy]
    rw [show ρ sM = MulAut.conj ybar from hybar.symm]
    exact inv_mul_cancel _
  have hkey' : ρ ⟨(y0 : G)⁻¹ * s, D.M.mul_mem (D.M.inv_mem (hYM hy0Y)) hsM⟩ = 1 := by
    have hEq : (⟨(y0 : G)⁻¹ * s, D.M.mul_mem (D.M.inv_mem (hYM hy0Y)) hsM⟩ : ↥D.M) =
        ⟨(y0 : G), hYM hy0Y⟩⁻¹ * sM := Subtype.ext rfl
    rw [hEq]
    exact hkey
  have hcC : (y0 : G)⁻¹ * s ∈ F08.CentOverO2 D.M Y := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.centOverO2_eq_ker_map hN]
    refine Subgroup.mem_map.mpr ⟨⟨(y0 : G)⁻¹ * s, ?_⟩, ?_, rfl⟩
    · exact D.M.mul_mem (D.M.inv_mem (hYM hy0Y)) hsM
    · rw [MonoidHom.mem_ker]
      exact hkey'
  have hprod : (y0 : G) * ((y0 : G)⁻¹ * s) = s := by group
  have hmem : (y0 : G) * ((y0 : G)⁻¹ * s) ∈ Y ⊔ F08.CentOverO2 D.M Y :=
    Subgroup.mul_mem_sup hy0Y hcC
  simpa [hprod] using hmem

theorem sylow_three_eq_sup_inf_centOverO2 {D : Data G} (h642 : P17_64_2 D 5 2)
    (hK : K_A5U34BorelQuotient) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M) :
    S = (S ⊓ S17.Lp D 5) ⊔ (S ⊓ F08.CentOverO2 D.M (S17.Lp D 5)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Subgroup G := S17.Lp D 5
  let C : Subgroup G := F08.CentOverO2 D.M Y
  have hYM : Y ≤ D.M := S17.Lp_le_M D 5
  have hMN : D.M ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hYM]
    exact s13_Lp_normal D.M 5
  have hCeq : C = centSection D.M Y (CFSG.Open.pCoreOf 2 Y) :=
    S17.centOverO2_eq_centSection
  have hCM : C ≤ D.M := by
    rw [hCeq]; exact centSection_le _ _ _
  have hCN : D.M ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCeq]; exact S17.centSection_le_normalizer hMN
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hS.le.trans hMN
  have hSC : S ≤ Subgroup.normalizer (C : Set G) := hS.le.trans hCN
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) := hYM.trans hCN
  have hcop : Nat.Coprime 3 (Nat.card (Y ⊓ C : Subgroup G)) := by
    have h2 : IsPGroup 2 ↥(Y ⊓ C) := by
      rw [hCeq]
      have hle : (S17.Lp D 5 ⊓ centSection D.M (S17.Lp D 5)
          (CFSG.Open.pCoreOf 2 (S17.Lp D 5))) ≤ CFSG.Open.pCoreOf 2 (S17.Lp D 5) := by
        rw [inf_comm]
        exact inf_centSection_Lp_le_pCore h642
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (S17.Lp D 5)).to_le hle
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr
      (by
        have h3 : ¬ 3 ∣ Nat.card ↥(Y ⊓ C) := fun hd =>
          CFSG.GroupTheory.not_dvd_card_of_isPGroup h2 Nat.prime_three (by norm_num) hd
        simpa using h3)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ Y) Y :=
    hS.inf_of_le_normalizer hYM hMN
  have hjoin := CFSG.GroupTheory.sup_inf_eq_of_isSylowOf_inf
    (p := 3) (S := S) (Y := Y) (C := C) hS.isPGroup
    (sylow_three_le_sup_centOverO2 h642 hK hS) hSY hSC hYC hcop hSyl
  exact hjoin.symm

theorem commutator_sylow_inf_centOverO2 {D : Data G} (h642 : P17_64_2 D 5 2)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M) :
    ⁅S ⊓ S17.Lp D 5, S ⊓ F08.CentOverO2 D.M (S17.Lp D 5)⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Subgroup G := S17.Lp D 5
  let C : Subgroup G := F08.CentOverO2 D.M Y
  have hYM : Y ≤ D.M := S17.Lp_le_M D 5
  have hMN : D.M ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hYM]
    exact s13_Lp_normal D.M 5
  have hCeq : C = centSection D.M Y (CFSG.Open.pCoreOf 2 Y) :=
    S17.centOverO2_eq_centSection
  have hCN : D.M ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCeq]; exact S17.centSection_le_normalizer hMN
  have hcop : Nat.Coprime 3 (Nat.card (Y ⊓ C : Subgroup G)) := by
    have h2 : IsPGroup 2 ↥(Y ⊓ C) := by
      rw [hCeq]
      have hle : (S17.Lp D 5 ⊓ centSection D.M (S17.Lp D 5)
          (CFSG.Open.pCoreOf 2 (S17.Lp D 5))) ≤ CFSG.Open.pCoreOf 2 (S17.Lp D 5) := by
        rw [inf_comm]
        exact inf_centSection_Lp_le_pCore h642
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (S17.Lp D 5)).to_le hle
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr
      (by
        have h3 : ¬ 3 ∣ Nat.card ↥(Y ⊓ C) := fun hd =>
          CFSG.GroupTheory.not_dvd_card_of_isPGroup h2 Nat.prime_three (by norm_num) hd
        simpa using h3)
  have hcomm : ⁅Y, C⁆ ≤ Y ⊓ C := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro y hy c hc
      have hcommO : c * y * c⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
        (mem_centSection_iff.mp (hCeq ▸ hc)).2.2.2 y hy
      have hmem : y * c * y⁻¹ * c⁻¹ = (c * y * c⁻¹ * y⁻¹)⁻¹ := by group
      rw [commutatorElement_def, hmem]
      exact (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) ((CFSG.Open.pCoreOf 2 Y).inv_mem hcommO)
    · rw [Subgroup.commutator_le]
      intro y hy c hc
      have hyM : y ∈ D.M := hYM hy
      have hyN : y ∈ Subgroup.normalizer (C : Set G) := hCN hyM
      have hconj : y * c * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hyN c).mp hc
      rw [commutatorElement_def]
      exact C.mul_mem hconj (C.inv_mem hc)
  exact CFSG.GroupTheory.commutator_inf_inf_eq_bot (p := 3) hS.isPGroup hcop hcomm

theorem pRank_three_bar2_Lp_eq_two {D : Data G} (h642 : P17_64_2 D 5 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 (S17.Lp D 5))) = 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : 3 ≠ 2 := by norm_num
  have hL2 : ∀ {A : Type} [Group A] [Finite A], IsL2 A 2 →
      CFSG.Open.pRank 3 (⊤ : Subgroup A) = 1 := by
    intro A _ _ hA
    have hSC : CFSG.Open.StatedClassicalModel A .PSL 2 2 2 :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA
    have hupper : CFSG.Open.pRank 3 (⊤ : Subgroup A) ≤ 1 :=
      CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even hSC hp hp2
    have h3dvd : 3 ∣ Nat.card A := by
      rw [S17.card_of_isL2 hA]
      norm_num
    have hlower : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup A) := by
      by_contra h
      have h0 : CFSG.Open.pRank 3 (⊤ : Subgroup A) = 0 := by omega
      have hnot : ¬ 3 ∣ Nat.card ↥(⊤ : Subgroup A) :=
        CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero hp (G := A) (H := ⊤) h0
      exact hnot (by simpa using h3dvd)
    omega
  have hU3 : ∀ {B : Type} [Group B] [Finite B], IsU3 B 2 →
      CFSG.Open.pRank 3 (⊤ : Subgroup B) = 1 := by
    intro B _ _ hB
    have h := Inputs1719.k_U3FourPowThreeRankOne_holds B 1 (by norm_num)
      (by simpa using hB)
    simpa using h
  rcases h642 with ⟨hsq, -⟩ | ⟨hu3, -⟩
  · obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := hsq
    have : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
    have : Finite B := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB)
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 (S17.Lp D 5))) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (A × B)) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (A × B)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup A) + CFSG.Open.pRank 3 (⊤ : Subgroup B) := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (A × B),
        ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 A,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 B]
      exact CFSG.Quasithin.H13.NQBlock.pRank_prod_eq hp
    rw [h1, h2, hL2 hA, hL2 hB]
  · obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := hu3
    have : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
    have : Finite B := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB)
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 (S17.Lp D 5))) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (A × B)) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (A × B)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup A) + CFSG.Open.pRank 3 (⊤ : Subgroup B) := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (A × B),
        ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 A,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 B]
      exact CFSG.Quasithin.H13.NQBlock.pRank_prod_eq hp
    rw [h1, h2, hL2 hA, hU3 hB]

theorem pRank_three_le_three_of_k_eq_two {D : Data G}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hns : ¬ Group.IsSolvable ↥D.M) (hk : D.k = 2) :
    CFSG.Open.pRank 3 D.M ≤ 3 := by
  by_contra h
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := by omega
  have h3sig : 3 ∈ D.sig := hSg.four_mem 3 Nat.prime_three (by norm_num) h4
  have hsub : 3 ∈ D.sig1 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg hns h3sig
  exact ((CFSG.LocalAnalysis.UniquenessCase.UC22.Data.k_eq_two_iff D).mp hk)
    (hSg.sig1_sp 3 hsub)

theorem pRank_three_sylow_inf_Lp_eq_two {D : Data G} (h642 : P17_64_2 D 5 2)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M) :
    CFSG.Open.pRank 3 (S ⊓ S17.Lp D 5) = 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Subgroup G := S17.Lp D 5
  have hYM : Y ≤ D.M := S17.Lp_le_M D 5
  have hMN : D.M ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hYM]
    exact s13_Lp_normal D.M 5
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ Y) Y :=
    hS.inf_of_le_normalizer hYM hMN
  have hA : CFSG.Open.pRank 3 (S ⊓ Y) = CFSG.Open.pRank 3 Y :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf Nat.prime_three hSyl
  have hY : CFSG.Open.pRank 3 Y =
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 Y)) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd
      Nat.prime_three (by norm_num)).symm
  rw [hA, hY]
  exact pRank_three_bar2_Lp_eq_two h642

theorem pRank_three_inf_centOverO2_le_one {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hk : D.k = 2)
    (h642 : P17_64_2 D 5 2) (hK : K_A5U34BorelQuotient) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M) :
    CFSG.Open.pRank 3 (S ⊓ F08.CentOverO2 D.M (S17.Lp D 5)) ≤ 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  let Y : Subgroup G := S17.Lp D 5
  let C : Subgroup G := F08.CentOverO2 D.M Y
  let A : Subgroup G := S ⊓ Y
  set R : Subgroup G := S ⊓ C with hR
  have hYM : Y ≤ D.M := S17.Lp_le_M D 5
  have hMN : D.M ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hYM]
    exact s13_Lp_normal D.M 5
  have hCeq : C = centSection D.M Y (CFSG.Open.pCoreOf 2 Y) :=
    S17.centOverO2_eq_centSection
  have hcop : Nat.Coprime 3 (Nat.card (Y ⊓ C : Subgroup G)) := by
    have h2 : IsPGroup 2 ↥(Y ⊓ C) := by
      rw [hCeq]
      have hle : (Y ⊓ centSection D.M Y (CFSG.Open.pCoreOf 2 Y)) ≤
          CFSG.Open.pCoreOf 2 Y := by
        rw [inf_comm]
        exact inf_centSection_Lp_le_pCore h642
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hle
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr
      (by
        have h3 : ¬ 3 ∣ Nat.card ↥(Y ⊓ C) := fun hd =>
          CFSG.GroupTheory.not_dvd_card_of_isPGroup h2 Nat.prime_three (by norm_num) hd
        simpa using h3)
  have hScop : Nat.Coprime (Nat.card S) (Nat.card (Y ⊓ C : Subgroup G)) := by
    obtain ⟨n, hn⟩ := hS.isPGroup.exists_card_eq
    rw [hn]
    exact hcop.pow_left n
  have hSinf : S ⊓ (Y ⊓ C) = ⊥ := Subgroup.inf_eq_bot_of_coprime hScop
  have hjoin : A ⊔ R = S := (sylow_three_eq_sup_inf_centOverO2 h642 hK hS).symm
  have hcommAR : ⁅A, R⁆ = ⊥ := commutator_sylow_inf_centOverO2 h642 hS
  have hcomm : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a := by
    intro a ha r hr
    have hmem : ⁅a, r⁆ ∈ ⁅A, R⁆ := Subgroup.commutator_mem_commutator ha hr
    rw [hcommAR] at hmem
    exact commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hmem)
  have hdisj : A ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ S ⊓ (Y ⊓ C) := ⟨hx.1.1, hx.1.2, hx.2.2⟩
    rw [hSinf] at hx'
    exact hx'
  have hdecomp : ∀ {s : G}, s ∈ S → ∃ a ∈ A, ∃ r ∈ R, a * r = s := by
    intro s hs
    have hs' : s ∈ A ⊔ R := by rw [hjoin]; exact hs
    exact CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hs'
  let e : ↥A × ↥R ≃* ↥S :=
    Subgroup.mulEquivProdOfInternalDirect A R S
      (show A ≤ S from inf_le_left) (show R ≤ S from inf_le_left)
      (fun {a r} ha hr => hcomm a ha r hr) hdisj hdecomp
  have hpc : ∀ H : Subgroup G, CFSG.Open.pRank 3 H = CFSG.pRank 3 ↥H := by
    intro H
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup H,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥H]
  have hsum : CFSG.Open.pRank 3 S = CFSG.Open.pRank 3 A + CFSG.Open.pRank 3 R := by
    calc CFSG.Open.pRank 3 S = CFSG.pRank 3 ↥S := hpc S
      _ = CFSG.pRank 3 (↥A × ↥R) := by
          rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥S,
            CFSG.SectionRank.pRank_eq_open_pRank_top 3 (↥A × ↥R)]
          exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e).symm
      _ = CFSG.pRank 3 ↥A + CFSG.pRank 3 ↥R :=
          CFSG.Quasithin.H13.NQBlock.pRank_prod_eq hp
      _ = CFSG.Open.pRank 3 A + CFSG.Open.pRank 3 R := by rw [hpc A, hpc R]
  have hA : CFSG.Open.pRank 3 A = 2 := pRank_three_sylow_inf_Lp_eq_two h642 hS
  rw [hA] at hsum
  have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
    pRank_three_le_three_of_k_eq_two hSg
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC h.hK) hk
  have hSleM : CFSG.Open.pRank 3 S ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hS.le
  rw [hsum] at hSleM
  omega

theorem isCyclic_inf_centOverO2 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hk : D.k = 2)
    (h642 : P17_64_2 D 5 2) (hK : K_A5U34BorelQuotient) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M) :
    IsCyclic ↥(S ⊓ F08.CentOverO2 D.M (S17.Lp D 5)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 : CFSG.Open.pRank 3 (S ⊓ F08.CentOverO2 D.M (S17.Lp D 5)) ≤ 1 :=
    pRank_three_inf_centOverO2_le_one h hSg hk h642 hK hS
  have hRp : IsPGroup 3 ↥(S ⊓ F08.CentOverO2 D.M (S17.Lp D 5)) :=
    hS.isPGroup.to_le inf_le_left
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one
    Nat.prime_three (by norm_num) hRp hR3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
