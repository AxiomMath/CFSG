module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62E9Centralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62UniqueMaxInU
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
import CFSG.LocalAnalysis.UniquenessCase.UC6Pgrp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC6 Subgroup

theorem mem_of_inU_le_centralizer_conj
    {G : Type} [Group G] {M A E : Subgroup G}
    (hM : Subgroup.normalizer (M : Set G) = M)
    (hCA : Subgroup.centralizer (A : Set G) ≤ M)
    (hE : CFSG.LocalAnalysis.UniquenessCase.UC6.InU M E) {g : G}
    (hEg : E ≤ Subgroup.centralizer
      ((CFSG.Open.uniqueFourConj g A : Subgroup G) : Set G)) :
    g ∈ M := by
  rw [inU_iff_fixed hM] at hE
  have hg' : g⁻¹ ∈ M := by
    apply hE.2
    intro x hx
    apply hCA
    rw [Subgroup.mem_centralizer_iff]
    simp only [inv_inv]
    intro a ha
    have ha' : g⁻¹ * a * g ∈ CFSG.Open.uniqueFourConj g A := by
      rw [mem_uniqueFourConj_iff]
      have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [e]
      exact ha
    have hcomm : (g⁻¹ * a * g) * x = x * (g⁻¹ * a * g) :=
      (Subgroup.mem_centralizer_iff.mp (hEg hx)) (g⁻¹ * a * g) ha'
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * x * g⁻¹) * a := by group
  simpa using M.inv_mem hg'

theorem inU_of_card_three_of_centralizer_le
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G} {L Q P A : Subgroup G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D) (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hE9 : ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = 3 →
      ∃ E : Subgroup G, E ≤ L ∧ E ≤ Subgroup.centralizer (Y : Set G) ∧
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hAM : A ≤ D.M) (hAc : Nat.card A = 3)
    (hCA : Subgroup.centralizer (A : Set G) ≤ D.M) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.InU D.M A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMself : Subgroup.normalizer (D.M : Set G) = D.M :=
    normalizer_eq_of_isMaxTwoLocal D.maxLocal
  refine (inU_iff_fixed hMself).2 ⟨hAM, ?_⟩
  intro g hg
  have hAgM : CFSG.Open.uniqueFourConj g A ≤ D.M := by
    intro y hy
    rw [mem_uniqueFourConj_iff] at hy
    have := hg (g * y * g⁻¹) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at this
  have hAgc : Nat.card (CFSG.Open.uniqueFourConj g A) = 3 := by
    unfold CFSG.Open.uniqueFourConj
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hAc]
  have hAgp : IsPGroup 3 (CFSG.Open.uniqueFourConj g A) :=
    IsPGroup.of_card (n := 1) (by rw [hAgc]; norm_num)
  obtain ⟨k, hkM, hkconj⟩ :=
    CFSG.GH74.GLS.C3.Layer2.exists_mem_conj_le_of_isSylowOf hP hAgM hAgp
  have hYc : Nat.card (CFSG.Open.uniqueFourConj (g * k) A) = 3 := by
    unfold CFSG.Open.uniqueFourConj
    rw [Subgroup.card_map_of_injective (MulAut.conj ((g * k)⁻¹)).injective, hAc]
  have hYP : CFSG.Open.uniqueFourConj (g * k) A ≤ P := by
    intro y hy
    rw [mem_uniqueFourConj_iff] at hy
    have hz : g⁻¹ * ((g * k) * y * (g * k)⁻¹) * g ∈
        CFSG.Open.uniqueFourConj g A := by
      rw [mem_uniqueFourConj_iff]
      have e : g * (g⁻¹ * ((g * k) * y * (g * k)⁻¹) * g) * g⁻¹ =
          (g * k) * y * (g * k)⁻¹ := by group
      rw [e]
      exact hy
    have hk := hkconj _ hz
    have e : k⁻¹ * (g⁻¹ * ((g * k) * y * (g * k)⁻¹) * g) * k = y := by group
    rwa [e] at hk
  obtain ⟨E, hEL, hEcY, hEel, hEcard⟩ := hE9 (CFSG.Open.uniqueFourConj (g * k) A) hYP hYc
  have hEInU : CFSG.LocalAnalysis.UniquenessCase.UC6.InU D.M E :=
    inU_of_isElemAbelian_card_nine_le_of_isSylowOf h63 hLM hQ hΓ hEL hEel hEcard
  have hgkM : g * k ∈ D.M :=
    mem_of_inU_le_centralizer_conj hMself hCA hEInU hEcY
  have e : g = (g * k) * k⁻¹ := by group
  rw [e]
  exact D.M.mul_mem hgkM (D.M.inv_mem hkM)

theorem inU_of_card_three_le_Q
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G} {L Q P A : Subgroup G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D) (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hLrank : 2 ≤ CFSG.Open.pRank 3 L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (h61 : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L))
    (hAQ : A ≤ Q) (hAc : Nat.card A = 3) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.InU D.M A := by
  have hAM : A ≤ D.M := hAQ.trans (hQ.le.trans hLM)
  have hA3 : IsPGroup 3 A :=
    IsPGroup.of_card (n := 1) (by rw [hAc]; norm_num)
  have hAne : A ≠ ⊥ := by
    rintro hbot
    rw [hbot, Subgroup.card_bot] at hAc
    norm_num at hAc
  have hCA : Subgroup.centralizer (A : Set G) ≤ D.M :=
    (Subgroup.centralizer_le_normalizer (A : Set G)).trans
      ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (p := 3) (k := 1) hAQ
        (one_le_pRank_of_ne_bot Nat.prime_three hA3 hAne)).trans hΓ)
  exact inU_of_card_three_of_centralizer_le h63 hLM hQ hΓ hP
    (fun Y hYP hYc => exists_isElemAbelian_card_nine_le_centralizer hQ hLrank h61 hYP hYc)
    hAM hAc hCA

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
