module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207LinLevi0
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  SP207Lin

namespace SP207Lin

variable {K : Type*} [Field K] {m : ℕ}

@[expose] def permSL [CharP K 2] (σ : Equiv.Perm (Fin m)) : SpecialLinearGroup (Fin m) K :=
  ⟨permMatrix m K σ, by
    rw [det_permMatrix]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, CharTwo.neg_eq]⟩

theorem permSL_apply [CharP K 2] (σ : Equiv.Perm (Fin m)) (p q : Fin m) :
    (permSL (K := K) σ : Matrix (Fin m) (Fin m) K) p q = if p = σ q then 1 else 0 :=
  rfl

theorem permSL_conj_apply [CharP K 2] {σ : Equiv.Perm (Fin m)} (hσ : ∀ a, σ (σ a) = a)
    (y : SpecialLinearGroup (Fin m) K) (p q : Fin m) :
    ((permSL σ)⁻¹ * y * permSL σ : SpecialLinearGroup (Fin m) K) p q =
      (y : Matrix (Fin m) (Fin m) K) (σ p) (σ q) := by
  have hg : (permSL (K := K) σ)⁻¹ = permSL σ := by
    refine inv_eq_of_mul_eq_one_right (Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_)
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, permSL_apply, hσ,
      Matrix.one_apply]
  rw [hg]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, permSL_apply]
  have h1 : ∀ j, (∑ r, (if p = σ r then (1 : K) else 0) * (y : Matrix (Fin m) (Fin m) K) r j) =
      y (σ p) j := fun j => by
    rw [Finset.sum_eq_single (σ p)]
    · simp [hσ]
    · intro r _ hr
      have : p ≠ σ r := fun h => hr (by rw [h, hσ])
      simp [this]
    · simp
  simp only [h1]
  simp

theorem exists_levi_witness_of_involution [CharP K 2] (hm : m ≤ 4) {I : Set ℕ}
    (σ : Equiv.Perm (Fin m)) (hσ : ∀ a, σ (σ a) = a)
    (hsep : ∀ p q : Fin m, CutBetween I q p → CutBetween I (σ q) (σ p) ∨ CutBetween I (σ p) (σ q))
    (hmove : ∃ i ∈ I, ∃ c : Fin m, (c : ℕ) < i ∧ i ≤ (σ c : ℕ)) :
    ∃ (R : Subgroup (SpecialLinearGroup (Fin m) K)) (g : SpecialLinearGroup (Fin m) K),
      IsPGroup 2 R ∧ R ≤ flagStabilizer m K I ∧ g ∉ flagStabilizer m K I ∧
      ∀ x ∈ flagStabilizer m K I, ∃ u ∈ R,
        u⁻¹ * x ∈ (flagStabilizer m K I).map (MulAut.conj g).toMonoidHom := by
  refine ⟨flagStabilizer m K I ⊓ unitriangular m K, permSL σ, fun u => ⟨2, ?_⟩, inf_le_left, ?_,
    fun x hx => ?_⟩
  · exact Subtype.ext (pow_eq_one_of_mem_unitriangular (k := 2) (by omega) u.2.2)
  · intro hg
    obtain ⟨i, hi, c, hc, hic⟩ := hmove
    have h := (mem_flagStabilizer_iff.1 hg) (σ c) c ⟨i, hi, hc, hic⟩
    simp [permSL_apply] at h
  · obtain ⟨u, huI, huU, hu⟩ := exists_unipotent_blockDiag hx
    refine ⟨u, ⟨huI, huU⟩, Subgroup.mem_map.2 ⟨(permSL σ)⁻¹ * (u⁻¹ * x) * permSL σ, ?_, ?_⟩⟩
    · refine mem_flagStabilizer_iff.2 fun p q hs => ?_
      rw [permSL_conj_apply hσ]
      exact hu _ _ (hsep p q hs)
    · simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      group

private theorem eq_of_three {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 3) (hI0 : I.Nonempty)
    (hI1 : I ≠ {1}) (hIm : I ≠ {2}) : I = ↑({1, 2} : Finset ℕ) := by
  have hsub : ∀ i ∈ I, i = 1 ∨ i = 2 := fun i hi => by have := hI i hi; omega
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · ext i
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨hsub i, by rintro (rfl | rfl) <;> assumption⟩
  · exact absurd (Set.ext fun i => by
      simp only [Set.mem_singleton_iff]
      exact ⟨fun hi => (hsub i hi).resolve_right fun h => h2 (h ▸ hi), by rintro rfl; exact h1⟩)
      hI1
  · exact absurd (Set.ext fun i => by
      simp only [Set.mem_singleton_iff]
      exact ⟨fun hi => (hsub i hi).resolve_left fun h => h1 (h ▸ hi), by rintro rfl; exact h2⟩)
      hIm
  · obtain ⟨i, hi⟩ := hI0
    rcases hsub i hi with rfl | rfl
    exacts [absurd hi h1, absurd hi h2]

private theorem eq_of_four {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 4) (hI0 : I.Nonempty)
    (hI1 : I ≠ {1}) (hIm : I ≠ {3}) :
    I = ↑({1, 2, 3} : Finset ℕ) ∨ I = ↑({1, 2} : Finset ℕ) ∨ I = ↑({2, 3} : Finset ℕ) ∨
      I = ↑({1, 3} : Finset ℕ) ∨ I = ↑({2} : Finset ℕ) := by
  have hsub : ∀ i ∈ I, i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by have := hI i hi; omega
  have key : ∀ S : Finset ℕ, (∀ i, i ∈ S ↔ (i = 1 ∨ i = 2 ∨ i = 3) ∧ i ∈ I) → I = ↑S :=
    fun S hS => Set.ext fun i =>
      ⟨fun hi => (hS i).2 ⟨hsub i hi, hi⟩, fun hi => ((hS i).1 hi).2⟩
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I <;> by_cases h3 : 3 ∈ I
  · exact Or.inl (key _ fun i => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun h => ⟨h, by rcases h with rfl | rfl | rfl <;> assumption⟩, fun h => h.1⟩)
  · exact Or.inr (Or.inl (key _ fun i => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      refine ⟨fun h => ⟨by omega, by rcases h with rfl | rfl <;> assumption⟩, fun h => ?_⟩
      rcases h.1 with rfl | rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl, absurd h.2 h3]))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ fun i => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      refine ⟨fun h => ⟨by omega, by rcases h with rfl | rfl <;> assumption⟩, fun h => ?_⟩
      rcases h.1 with rfl | rfl | rfl
      exacts [Or.inl rfl, absurd h.2 h2, Or.inr rfl]))))
  · exact absurd (Set.ext fun i => by
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hi => ?_, by rintro rfl; exact h1⟩
      rcases hsub i hi with rfl | rfl | rfl
      exacts [rfl, absurd hi h2, absurd hi h3]) hI1
  · exact Or.inr (Or.inr (Or.inl (key _ fun i => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      refine ⟨fun h => ⟨by omega, by rcases h with rfl | rfl <;> assumption⟩, fun h => ?_⟩
      rcases h.1 with rfl | rfl | rfl
      exacts [absurd h.2 h1, Or.inl rfl, Or.inr rfl])))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (key _ fun i => by
      simp only [Finset.mem_singleton]
      refine ⟨fun h => ⟨by omega, h ▸ h2⟩, fun h => ?_⟩
      rcases h.1 with rfl | rfl | rfl
      exacts [absurd h.2 h1, rfl, absurd h.2 h3]))))
  · exact absurd (Set.ext fun i => by
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hi => ?_, by rintro rfl; exact h3⟩
      rcases hsub i hi with rfl | rfl | rfl
      exacts [absurd hi h1, absurd hi h2, rfl]) hIm
  · obtain ⟨i, hi⟩ := hI0
    rcases hsub i hi with rfl | rfl | rfl
    exacts [absurd hi h1, absurd hi h2, absurd hi h3]

end SP207Lin

theorem uc22sp207_exists_levi_witness {m : ℕ} (hm : m = 3 ∨ m = 4) {K : Type} [Field K]
    [CharP K 2] {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < m) (hI0 : I.Nonempty) (hI1 : I ≠ {1})
    (hIm : I ≠ {m - 1}) :
    ∃ (R : Subgroup (SpecialLinearGroup (Fin m) K)) (g : SpecialLinearGroup (Fin m) K),
      IsPGroup 2 R ∧ R ≤ LinearFlag.flagStabilizer m K I ∧
      g ∉ LinearFlag.flagStabilizer m K I ∧
      ∀ x ∈ LinearFlag.flagStabilizer m K I, ∃ u ∈ R,
        u⁻¹ * x ∈ (LinearFlag.flagStabilizer m K I).map (MulAut.conj g).toMonoidHom := by
  rcases hm with rfl | rfl
  · obtain rfl := eq_of_three hI hI0 hI1 hIm
    exact exists_levi_witness_of_involution (by norm_num) (Equiv.swap 0 1) (by decide)
      (by simp only [CutBetween, Finset.mem_coe]; decide) (by simp only [Finset.mem_coe]; decide)
  · rcases eq_of_four hI hI0 hI1 hIm with rfl | rfl | rfl | rfl | rfl
    · exact exists_levi_witness_of_involution (by norm_num) (Equiv.swap 0 1) (by decide)
        (by simp only [CutBetween, Finset.mem_coe]; decide) (by simp only [Finset.mem_coe]; decide)
    · exact exists_levi_witness_of_involution (by norm_num) (Equiv.swap 0 1) (by decide)
        (by simp only [CutBetween, Finset.mem_coe]; decide) (by simp only [Finset.mem_coe]; decide)
    · exact exists_levi_witness_of_involution (by norm_num) (Equiv.swap 2 3) (by decide)
        (by simp only [CutBetween, Finset.mem_coe]; decide) (by simp only [Finset.mem_coe]; decide)
    · exact exists_levi_witness_of_involution (by norm_num) (Equiv.swap 0 3) (by decide)
        (by simp only [CutBetween, Finset.mem_coe]; decide) (by simp only [Finset.mem_coe]; decide)
    · exact exists_levi_witness_of_involution (by norm_num) (Equiv.swap 0 2 * Equiv.swap 1 3)
        (by decide) (by simp only [CutBetween, Finset.mem_coe]; decide)
        (by simp only [Finset.mem_coe]; decide)

end CFSG.LocalAnalysis.UniquenessCase.UC22
