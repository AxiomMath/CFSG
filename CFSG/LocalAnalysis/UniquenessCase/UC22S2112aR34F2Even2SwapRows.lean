module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step23
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitUnitaryGeometry
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwo
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront14

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ComponentClassification.AS81.Sec2 (conjSetStab conjPermHom)

private theorem uc22s2112r34_swaprows_ne_bot_of_equiv_perm_two
    {G : Type*} [Group G] {H : Subgroup G}
    (h : Nonempty (H ≃* Equiv.Perm (Fin 2))) : H ≠ ⊥ := by
  obtain ⟨e⟩ := h
  exact (Subgroup.nontrivial_iff_ne_bot H).mp (Equiv.nontrivial e.toEquiv)


theorem uc22s2112r34_exists_swap_of_ne_bot {X : Type} [Group X] [Finite X] {q : ℕ}
    (P : Sylow 2 X)
    (hnt : (conjPermHom (le_refl (conjSetStab (FunSet (fundPred q) X (P : Subgroup X))))).range ≠
      ⊥)
    (h2 : (FunSet (fundPred q) X (P : Subgroup X)).ncard = 2) {K₁ K₂ : Subgroup X}
    (h₁ : K₁ ∈ FunSet (fundPred q) X (P : Subgroup X))
    (h₂ : K₂ ∈ FunSet (fundPred q) X (P : Subgroup X)) (hne : K₁ ≠ K₂) :
    ∃ w ∈ (P : Subgroup X), K₁.map (MulAut.conj w).toMonoidHom = K₂ := by
  classical
  let Δ := FunSet (fundPred q) X (P : Subgroup X)
  let N := conjSetStab Δ
  let ρ := conjPermHom (le_refl N)
  have hPN : (P : Subgroup X) ≤ N :=
    F14.sylow_le_conjSetStab_funSet
      (fun g _ hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK) P
  have hΔ : Δ = {K₁, K₂} := by
    have hsub : ({K₁, K₂} : Set (Subgroup X)) ⊆ Δ := by
      intro K hK
      rcases hK with rfl | rfl
      · exact h₁
      · exact h₂
    have hcard : ({K₁, K₂} : Set (Subgroup X)).ncard = 2 := Set.ncard_pair hne
    have hle : Δ.ncard ≤ ({K₁, K₂} : Set (Subgroup X)).ncard := by
      have hΔcard : Δ.ncard = 2 := h2
      omega
    exact (Set.eq_of_subset_of_ncard_le hsub hle).symm
  by_contra hno
  push Not at hno
  have hker : (P : Subgroup X).subgroupOf N ≤ ρ.ker := by
    intro w hw
    have hwP : (w : X) ∈ (P : Subgroup X) := Subgroup.mem_subgroupOf.mp hw
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun V => ?_
    have hV : (V : Subgroup X) = K₁ ∨ (V : Subgroup X) = K₂ := by
      let a : Subgroup X := (V : Subgroup X)
      have ha : a ∈ Δ := V.2
      have hmem : a ∈ ({K₁, K₂} : Set (Subgroup X)) := by
        rw [hΔ] at ha
        exact ha
      simpa only [a, Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    have hfix₁ : ρ w ⟨K₁, h₁⟩ = ⟨K₁, h₁⟩ := by
      apply Subtype.ext
      let a : Subgroup X := (ρ w ⟨K₁, h₁⟩ : ↥Δ)
      change a = K₁
      have himg : a = K₁.map (MulAut.conj (w : X)).toMonoidHom := by
        change ((conjPermHom (le_refl N) w ⟨K₁, h₁⟩ : ↥Δ) : Subgroup X) =
          K₁.map (MulAut.conj (w : X)).toMonoidHom
        rw [CFSG.ComponentClassification.AS81.Sec2.conjPermHom_apply]
        simp only [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate, inv_inv]
      have ha : a ∈ Δ := (ρ w ⟨K₁, h₁⟩).2
      have hmem : a ∈ ({K₁, K₂} : Set (Subgroup X)) := by
        rw [hΔ] at ha
        exact ha
      rw [himg] at hmem ⊢
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · exact h
      · exact absurd h (hno (w : X) hwP)
    have hfix₂ : ρ w ⟨K₂, h₂⟩ = ⟨K₂, h₂⟩ := by
      apply Subtype.ext
      let a : Subgroup X := (ρ w ⟨K₂, h₂⟩ : ↥Δ)
      change a = K₂
      have himg : a = K₂.map (MulAut.conj (w : X)).toMonoidHom := by
        change ((conjPermHom (le_refl N) w ⟨K₂, h₂⟩ : ↥Δ) : Subgroup X) =
          K₂.map (MulAut.conj (w : X)).toMonoidHom
        rw [CFSG.ComponentClassification.AS81.Sec2.conjPermHom_apply]
        simp only [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate, inv_inv]
      have ha : a ∈ Δ := (ρ w ⟨K₂, h₂⟩).2
      have hmem : a ∈ ({K₁, K₂} : Set (Subgroup X)) := by
        rw [hΔ] at ha
        exact ha
      rw [himg] at hmem ⊢
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · exfalso
        have heq : ρ w ⟨K₂, h₂⟩ = ρ w ⟨K₁, h₁⟩ := by
          apply Subtype.ext
          change a = ↑(ρ w ⟨K₁, h₁⟩)
          rw [himg, h]
          exact (congrArg Subtype.val hfix₁).symm
        exact hne (congrArg Subtype.val ((ρ w).injective heq)).symm
      · exact h
    rcases hV with hV | hV
    · rw [show V = ⟨K₁, h₁⟩ from Subtype.ext hV]
      simpa using hfix₁
    · rw [show V = ⟨K₂, h₂⟩ from Subtype.ext hV]
      simpa using hfix₂
  have hcard_range : Nat.card ρ.range = 2 := by
    have hperm : Nat.card (Equiv.Perm ↥Δ) = 2 := by
      rw [Nat.card_perm, Nat.card_coe_set_eq, h2]
      norm_num
    have hdvd : Nat.card ρ.range ∣ 2 := by
      simpa [hperm] using Subgroup.card_subgroup_dvd_card ρ.range
    have hne_one : Nat.card ρ.range ≠ 1 := by
      intro h
      exact hnt (Subgroup.eq_bot_of_card_eq ρ.range h)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne_one
    · exact h
  have hker_index : ρ.ker.index = 2 := by
    rw [Subgroup.index_ker, hcard_range]
  have hP_index : ((P : Subgroup X).subgroupOf N).index ∣ (P : Subgroup X).index := by
    have hmul := Subgroup.relIndex_mul_index hPN
    rw [show ((P : Subgroup X).subgroupOf N).index = (P : Subgroup X).relIndex N from rfl]
    rw [← hmul]
    exact dvd_mul_right _ _
  have htwo_dvd : 2 ∣ (P : Subgroup X).index := by
    have h := dvd_trans (Subgroup.index_dvd_of_le hker) hP_index
    rwa [hker_index] at h
  exact P.not_dvd_index htwo_dvd

theorem uc22s2112r34_exists_swap_of_lieModel {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hrow : (t = .PSL ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSU ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSp ∧ n = 2))
    (P : Sylow 2 X) {K₁ K₂ : Subgroup X}
    (h₁ : K₁ ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X))
    (h₂ : K₂ ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X)) (hne : K₁ ≠ K₂) :
    ∃ w ∈ (P : Subgroup X), K₁.map (MulAut.conj w).toMonoidHom = K₂ := by
  have htwo : FunTwoType t n := by
    rcases hrow with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [FunTwoType]
  have h2 := ncard_funSet_eq_two_of_funTwoType hp hp2 hadm hX htwo P
  have hnt : (conjPermHom (le_refl (conjSetStab (FunSet (fundPred (p ^ f)) X
      (P : Subgroup X))))).range ≠ ⊥ := by
    have : Fact p.Prime := ⟨hp⟩
    rcases hrow with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · exact uc22s2112r34_swaprows_ne_bot_of_equiv_perm_two (by
        simpa using nonempty_equiv_perm_funSet_psl_even (m := 1) hp2 le_rfl hadm hX P)
    · exact uc22s2112r34_swaprows_ne_bot_of_equiv_perm_two (by
        simpa using nonempty_equiv_perm_funSet_psl_odd (m := 1) hp2 le_rfl hadm hX P)
    · exact uc22s2112r34_swaprows_ne_bot_of_equiv_perm_two (by
        simpa using nonempty_equiv_perm_funSet_psu_even (m := 1) hp2 le_rfl hadm hX P)
    · exact uc22s2112r34_swaprows_ne_bot_of_equiv_perm_two (by
        simpa using nonempty_equiv_perm_funSet_psu_odd (m := 1) hp2 le_rfl hadm hX P)
    · exact uc22s2112r34_swaprows_ne_bot_of_equiv_perm_two (by
        simpa using nonempty_equiv_perm_funSet_psp hp2 hadm hX P)
  exact uc22s2112r34_exists_swap_of_ne_bot P hnt h2 h₁ h₂ hne

end CFSG.LocalAnalysis.UniquenessCase.UC22
