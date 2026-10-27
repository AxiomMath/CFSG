module

public import CFSG.Timmesfeld.ARS.Sec5Lines
public import CFSG.Timmesfeld.ARS.Sec3PlaneGroup

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

theorem stabSet_le_normalizer_gen (Δ : Set (Subgroup G)) :
    stabSet Δ ≤ Subgroup.normalizer ((gen Δ : Subgroup G) : Set G) := fun _ hg =>
  conjSub_eq_self_iff.1 (by rw [conjSub_gen, mem_stabSet.1 hg])

section Centralizer

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem exists_mem_lambdaSet_of_commuting_gen (hΔ : IsWeakTI R Δ) {C : Subgroup G}
    (hC : C ∈ R) (hCV : Commuting C (gen Δ)) (hCΔ : C ∉ Δ) :
    ∃ C' ∈ R, Commuting C' (gen Δ) ∧ C' ∉ Δ ∧ ∃ A ∈ Δ, C' ∈ lambdaSet R A := by
  obtain ⟨A, hA, -⟩ := hΔ.2.1
  have hAR := hΔ.1 hA
  have hAC : Commuting A C := (hCV.mono le_rfl (le_gen hA)).symm
  by_cases hCl : C ∈ lambdaSet R A
  · exact ⟨C, hC, hCV, hCΔ, A, hA, hCl⟩
  have hCA : C ≠ A := fun e => hCΔ (e ▸ hA)
  obtain ⟨F, hF, hCF⟩ : ∃ F ∈ lambdaSet R A, ¬ Commuting C F := by
    by_contra! hall
    have hCM : Commuting C (M R A) := commuting_iff_le_centralizer.2
      (sup_le (commuting_iff_le_centralizer.1 hAC.symm)
        (iSup₂_le fun F hF => commuting_iff_le_centralizer.1 (hall F hF)))
    have hmem : C ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨hC, hCM⟩
    rw [setOf_commuting_M_eq_singleton hR hiso hnd hΩ hAR] at hmem
    exact hCA hmem
  have hFR : F ∈ R := hF.1.1
  have hne : C ≠ F := fun e => hCl (e ▸ hF)
  have hs : Special R C F := by
    rcases hR.rel C hC F hFR hne with h | h | h
    · exact absurd h hCF
    · exact absurd hAC.symm
        (not_commuting_of_opposite_of_mem_lambdaSet hR hC h (mem_lambdaSet_comm hAR hF))
    · exact h
  have hDl := mem_lambdaSet_commutator hR hiso hC hFR hs
  have hDM : ⁅C, F⁆ ≤ M R A := by
    rw [Subgroup.commutator_le]
    intro c hc f hf
    have hcn := QD.le_normalizer_M hR hAR (⟨hC, hAC⟩ : C ∈ centralSet R A) hc
    have hfM : f ∈ M R A := QD.le_M hF hf
    rw [commutatorElement_def]
    exact (M R A).mul_mem ((Subgroup.mem_normalizer_iff.1 hcn f).1 hfM) ((M R A).inv_mem hfM)
  have hDA : ⁅C, F⁆ ≠ A := fun e => hCl (e ▸ hDl.1)
  have hDΛ := mem_lambdaSet_of_le_M hR hiso hnd hΩ hAR hs.1 hDM hDA
  have hFn : F ≤ Subgroup.normalizer ((gen Δ : Subgroup G) : Set G) :=
    (le_stabSet_of_commuting hR hΔ hFR hA hF.1.2.2.symm).trans (stabSet_le_normalizer_gen Δ)
  have hDV : Commuting ⁅C, F⁆ (gen Δ) := QD.commuting_commutator hCV hFn
  by_cases hDΔ : ⁅C, F⁆ ∈ Δ
  · exact ⟨C, hC, hCV, hCΔ, _, hDΔ, hDl.1⟩
  · exact ⟨_, hs.1, hDV, hDΔ, A, hA, hDΛ⟩

omit hiso hnd hΩ in
theorem not_opposite_of_commuting_gen {C A₀ F : Subgroup G} (hC : C ∈ R)
    (hCV : Commuting C (gen Δ)) (hA₀ : A₀ ∈ Δ) (hA₀R : A₀ ∈ R) (hCA₀ : C ∈ lambdaSet R A₀)
    (hF : F ∈ R) (hFs : F ≤ stabSet Δ) : ¬ Opposite C F := by
  intro hCF
  obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hF
  have hfn := stabSet_le_normalizer_gen Δ (hFs hf)
  have hCfV : Commuting (conjSub C f) (gen Δ) := by
    have := hCV.conjSub f
    rwa [conjSub_eq_self_iff.2 hfn] at this
  have hne : conjSub C 1 ≠ conjSub C f := by
    rw [conjSub_one]
    intro h
    exact hf1 (hCF.symm.eq_one_of_conjSub_eq hf h.symm)
  have hsup := hCF.sup_conjSub_eq (hR.mul_self C hC) (one_mem _) (Subgroup.mem_sup_right hf) hne
  rw [conjSub_one] at hsup
  have hFV : Commuting F (gen Δ) :=
    (hCV.sup_left hCfV).mono (le_sup_right.trans hsup.symm.le) le_rfl
  exact not_commuting_of_opposite_of_mem_lambdaSet hR hF hCF.symm (mem_lambdaSet_comm hA₀R hCA₀)
    (hFV.mono le_rfl (le_gen hA₀))

theorem mem_lambdaSet_of_mem (hΔ : IsWeakTI R Δ) {C A₀ : Subgroup G} (hC : C ∈ R)
    (hCV : Commuting C (gen Δ)) (hCΔ : C ∉ Δ) (hA₀ : A₀ ∈ Δ) (hCA₀ : C ∈ lambdaSet R A₀)
    {A : Subgroup G} (hA : A ∈ Δ) : C ∈ lambdaSet R A := by
  have hAR := hΔ.1 hA
  have hI : C ∈ isolatedSet R A := ⟨⟨hC, (hCV.mono le_rfl (le_gen hA)).symm⟩, fun X hX =>
    not_opposite_of_commuting_gen hR hC hCV hA₀ (hΔ.1 hA₀) hCA₀ hX.1
      (le_stabSet_of_commuting hR hΔ hX.1 hA hX.2.symm)⟩
  rw [QD.isolatedSet_eq hR hiso hnd hΩ hAR] at hI
  exact hI.resolve_left fun e => hCΔ (e ▸ hA)

theorem mem_of_commuting_gen (hΔ : IsWeakTI R Δ) {C : Subgroup G} (hC : C ∈ R)
    (hCV : Commuting C (gen Δ)) : C ∈ Δ := by
  by_contra hCΔ
  obtain ⟨C, hC, hCV, hCΔ, A₀, hA₀, hCA₀⟩ :=
    exists_mem_lambdaSet_of_commuting_gen hR hiso hnd hΩ hΔ hC hCV hCΔ
  have hall : ∀ A ∈ Δ, A ∈ lambdaSet R C := fun A hA =>
    mem_lambdaSet_comm (hΔ.1 hA) (mem_lambdaSet_of_mem hR hiso hnd hΩ hΔ hC hCV hCΔ hA₀ hCA₀ hA)
  have hQ := Q_eq_M_of_omegaSet hR hiso hnd hΩ hC
  have hVM : gen Δ ≤ M R C := gen_le fun A hA => QD.le_M (hall A hA)
  have hU : ∀ U ∈ lambdaSet R C, Commuting U (gen Δ) := by
    intro U hUl
    have hUR : U ∈ R := hUl.1.1
    have hsp : ∀ E ∈ Δ, ¬ Commuting U E → Special R E U ∧ ⁅E, U⁆ = C := by
      intro E hE hUE
      have hER := hΔ.1 hE
      have hne : E ≠ U := fun e => hUE (e ▸ hR.commuting_self hER)
      have hs : Special R E U := by
        rcases hR.rel E hER U hUR hne with h | h | h
        · exact absurd h.symm hUE
        · exact absurd (hCV.mono le_rfl (le_gen hE)).symm
            (not_commuting_of_opposite_of_mem_lambdaSet hR hER h (mem_lambdaSet_comm hC hUl))
        · exact h
      refine ⟨hs, QD.eq_of_le_of_mem hR hiso hs.1 hC ?_⟩
      rw [← hQ.2.2.1]
      exact Subgroup.commutator_mono ((le_gen hE).trans hVM) (QD.le_M hUl)
    by_contra hUV
    obtain ⟨B, hB, hUB⟩ : ∃ B ∈ Δ, ¬ Commuting U B := by
      by_contra! h
      exact hUV (commuting_iff_le_centralizer.2
        (gen_le fun B hB => commuting_iff_le_centralizer.1 (h B hB)))
    obtain ⟨hsB, hBU⟩ := hsp B hB hUB
    by_cases hex : ∃ A ∈ Δ, Commuting U A
    · obtain ⟨A, hA, hUA⟩ := hex
      have := commutator_mem hR hiso hΔ hB hUR hA hUA hsB
      rw [hBU] at this
      exact hCΔ this
    simp only [not_exists, not_and] at hex
    obtain ⟨A₁, hA₁, A₂, hA₂, hA₁₂⟩ := hΔ.2.1
    obtain ⟨hs₁, h₁⟩ := hsp A₁ hA₁ (hex A₁ hA₁)
    obtain ⟨hs₂, h₂⟩ := hsp A₂ hA₂ (hex A₂ hA₂)
    obtain ⟨u, hu, hu1⟩ := hR.exists_ne_one hUR
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hΔ.1 hA₁)
    have hauC : ⁅a, u⁆ ∈ C := h₁ ▸ Subgroup.commutator_mem_commutator ha hu
    obtain ⟨b, hb, hbu⟩ := (bijOn_commutator_left hR hiso (hΔ.1 hA₂) hUR hs₂ hu hu1).surjOn
      (h₂.symm ▸ hauC : ⁅a, u⁆ ∈ ⁅A₂, U⁆)
    have hbu' : ⁅b, u⁆ = ⁅a, u⁆ := hbu
    have hcomm : Commute a ⁅b, u⁆ :=
      (hCV _ (hbu' ▸ hauC) a (le_gen hA₁ ha)).symm
    have habu : ⁅a * b, u⁆ = 1 := by
      rw [Plane.commutatorElement_mul_left_of_commute hcomm, hbu']
      exact hR.mul_self C hC _ hauC
    have hab1 : a * b ≠ 1 := by
      intro h1
      have hmem : a ∈ A₁ ⊓ A₂ := ⟨ha, by rw [eq_inv_of_mul_eq_one_left h1]; exact A₂.inv_mem hb⟩
      rw [inf_eq_bot hR hiso (hΔ.1 hA₁) (hΔ.1 hA₂) hA₁₂, Subgroup.mem_bot] at hmem
      exact ha1 hmem
    obtain ⟨E, hE, -, habE⟩ := exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ subset_rfl
      ((gen Δ).mul_mem (le_gen hA₁ ha) (le_gen hA₂ hb)) hab1
    exact hu1 (eq_one_of_commute_of_special hR hiso (hΔ.1 hE) hUR (hsp E hE (hex E hE)).1 habE
      hab1 hu ((commutatorElement_eq_one_iff_mul_comm).1 habu))
  have hMV : Commuting (gen Δ) (M R C) := commuting_iff_le_centralizer.2
    (sup_le (commuting_iff_le_centralizer.1 hCV.symm)
      (iSup₂_le fun U hUl => commuting_iff_le_centralizer.1 (hU U hUl).symm))
  have hmem : A₀ ∈ {B | B ∈ R ∧ Commuting B (M R C)} :=
    ⟨hΔ.1 hA₀, hMV.mono (le_gen hA₀) le_rfl⟩
  rw [setOf_commuting_M_eq_singleton hR hiso hnd hΩ hC] at hmem
  exact hCΔ (hmem ▸ hA₀)

theorem setOf_commuting_gen_eq (hΔ : IsWeakTI R Δ) :
    {C | C ∈ R ∧ Commuting C (gen Δ)} = Δ := by
  ext C
  refine ⟨fun h => mem_of_commuting_gen hR hiso hnd hΩ hΔ h.1 h.2, fun h => ⟨hΔ.1 h, ?_⟩⟩
  exact (commuting_gen_of_isWeakTI_of hR hiso hnd hΔ).mono (le_gen h) le_rfl

theorem gen_le_M (hΔ : IsWeakTI R Δ) {A : Subgroup G} (hA : A ∈ Δ) : gen Δ ≤ M R A :=
  gen_le fun D hD => by
    by_cases hDA : D = A
    · exact hDA ▸ QD.le_M_self
    · exact QD.le_M (mem_lambdaSet hR hiso hnd hΩ hΔ hA hD (Ne.symm hDA))

theorem commutator_gen_le (hΔ : IsWeakTI R Δ) {A E : Subgroup G} (hA : A ∈ Δ)
    (hE : E ∈ lambdaSet R A) : ⁅gen Δ, E⁆ ≤ A := by
  rw [← (Q_eq_M_of_omegaSet hR hiso hnd hΩ (hΔ.1 hA)).2.2.1]
  exact Subgroup.commutator_mono (gen_le_M hR hiso hnd hΩ hΔ hA) (QD.le_M hE)

theorem subset_of_mem_of_mem (hΔ : IsWeakTI R Δ) {Δ' : Set (Subgroup G)}
    (hΔ' : IsWeakTI R Δ') {A B : Subgroup G} (hA : A ∈ Δ) (hA' : A ∈ Δ') (hB : B ∈ Δ)
    (hB' : B ∈ Δ') (hAB : A ≠ B) : Δ' ⊆ Δ := by
  intro E hE
  by_cases hEA : E = A
  · exact hEA ▸ hA
  by_cases hEB : E = B
  · exact hEB ▸ hB
  have h1 := commutator_gen_le hR hiso hnd hΩ hΔ hA
    (mem_lambdaSet hR hiso hnd hΩ hΔ' hA' hE (Ne.symm hEA))
  have h2 := commutator_gen_le hR hiso hnd hΩ hΔ hB
    (mem_lambdaSet hR hiso hnd hΩ hΔ' hB' hE (Ne.symm hEB))
  have hbot : ⁅gen Δ, E⁆ = ⊥ := by
    rw [eq_bot_iff, ← inf_eq_bot hR hiso (hΔ.1 hA) (hΔ.1 hB) hAB]
    exact le_inf h1 h2
  exact mem_of_commuting_gen hR hiso hnd hΩ hΔ (hΔ'.1 hE)
    (commuting_iff_commutator_eq_bot.2 hbot).symm

theorem eq_of_mem_of_mem (hΔ : IsWeakTI R Δ) {Δ' : Set (Subgroup G)} (hΔ' : IsWeakTI R Δ')
    (hcard : Nat.card Δ' = Nat.card Δ) {A B : Subgroup G} (hA : A ∈ Δ) (hA' : A ∈ Δ')
    (hB : B ∈ Δ) (hB' : B ∈ Δ') (hAB : A ≠ B) : Δ' = Δ := by
  have hsub := subset_of_mem_of_mem hR hiso hnd hΩ hΔ hΔ' hA hA' hB hB' hAB
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]

end Centralizer

end Sec5

end CFSG.Timmesfeld.ARS
