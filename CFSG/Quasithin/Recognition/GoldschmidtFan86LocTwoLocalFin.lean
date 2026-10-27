module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Fan86

open Equiv

theorem eq_one_of_pow_three_eq_one {G : Type*} [Group G] (hG : IsPGroup 2 G) {w : G}
    (h3 : w ^ 3 = 1) : w = 1 := by
  obtain ⟨m, hm⟩ := hG w
  exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3))).1
    ⟨hm, h3⟩

theorem conj_pow_mem {G : Type*} [Group G] {K : Subgroup G} {ξ : G}
    (hN : ∀ k ∈ K, ξ * k * ξ⁻¹ ∈ K) {k : G} (hk : k ∈ K) (i : ℕ) :
    ξ ^ i * k * (ξ ^ i)⁻¹ ∈ K := by
  induction i with
  | zero => simpa using hk
  | succ i ih =>
    have := hN _ ih
    have e : ξ ^ (i + 1) * k * (ξ ^ (i + 1))⁻¹ = ξ * (ξ ^ i * k * (ξ ^ i)⁻¹) * ξ⁻¹ := by group
    rw [e]
    exact this

theorem eq_one_of_conj_mul {G : Type*} [Group G] {K : Subgroup G} (hK : IsPGroup 2 K) {ξ : G}
    (hN : ∀ k ∈ K, ξ * k * ξ⁻¹ ∈ K) {k : G} (hk : k ∈ K) (i j : ℕ)
    (h3 : ((ξ ^ i * k * (ξ ^ i)⁻¹) * (ξ ^ j * k * (ξ ^ j)⁻¹)) ^ 3 = 1) :
    (ξ ^ i * k * (ξ ^ i)⁻¹) * (ξ ^ j * k * (ξ ^ j)⁻¹) = 1 := by
  have hw : (ξ ^ i * k * (ξ ^ i)⁻¹) * (ξ ^ j * k * (ξ ^ j)⁻¹) ∈ K :=
    K.mul_mem (conj_pow_mem hN hk i) (conj_pow_mem hN hk j)
  have := eq_one_of_pow_three_eq_one hK (w := ⟨_, hw⟩) (Subtype.ext (by simpa using h3))
  simpa using congrArg Subtype.val this

@[expose] def IsKlein4 (v : Perm (Fin 4)) : Prop := v = 1 ∨ (v * v = 1 ∧ ∀ i, v i ≠ i)

instance (v : Perm (Fin 4)) : Decidable (IsKlein4 v) := by unfold IsKlein4; infer_instance

theorem isKlein4_conj {v : Perm (Fin 4)} (hv : IsKlein4 v) (σ : Perm (Fin 4)) :
    IsKlein4 (σ * v * σ⁻¹) := by
  rcases hv with rfl | ⟨h2, hfix⟩
  · left
    simp
  · right
    refine ⟨?_, fun i hi => hfix (σ⁻¹ i) ?_⟩
    · have : σ * v * σ⁻¹ * (σ * v * σ⁻¹) = σ * (v * v) * σ⁻¹ := by group
      rw [this, h2]
      group
    · have h : σ (v (σ⁻¹ i)) = σ (σ⁻¹ i) := by simpa using hi
      exact σ.injective h

theorem conj_ne_one {G : Type*} [Group G] {v : G} (hv : v ≠ 1) (σ : G) : σ * v * σ⁻¹ ≠ 1 := by
  intro h
  apply hv
  calc v = σ⁻¹ * (σ * v * σ⁻¹) * σ := by group
    _ = 1 := by rw [h]; group

theorem fact_three : ∀ ξ k : Perm (Fin 3), ξ ^ 3 = 1 → ξ ≠ 1 → k ≠ 1 →
    ∃ i j : Fin 3, ((ξ ^ i.val * k * (ξ ^ i.val)⁻¹) * (ξ ^ j.val * k * (ξ ^ j.val)⁻¹)) ^ 3 = 1 ∧
      (ξ ^ i.val * k * (ξ ^ i.val)⁻¹) * (ξ ^ j.val * k * (ξ ^ j.val)⁻¹) ≠ 1 := by
  decide +kernel

theorem fact_four : ∀ ξ k : Perm (Fin 4), ξ ^ 3 = 1 → ξ ≠ 1 → ¬ IsKlein4 k →
    ∃ i j : Fin 3, ((ξ ^ i.val * k * (ξ ^ i.val)⁻¹) * (ξ ^ j.val * k * (ξ ^ j.val)⁻¹)) ^ 3 = 1 ∧
      (ξ ^ i.val * k * (ξ ^ i.val)⁻¹) * (ξ ^ j.val * k * (ξ ^ j.val)⁻¹) ≠ 1 := by
  decide +kernel

set_option synthInstance.maxSize 2000 in
theorem fact_orbit : ∀ ξ v w : Perm (Fin 4), ξ ^ 3 = 1 → ξ ≠ 1 → IsKlein4 v → v ≠ 1 →
    IsKlein4 w → w ≠ 1 → ∃ j : Fin 3, ξ ^ j.val * v * (ξ ^ j.val)⁻¹ = w := by
  decide +kernel

theorem eq_one_of_normalized_three {ξ : Perm (Fin 3)} (h3 : ξ ^ 3 = 1) (h1 : ξ ≠ 1)
    {K : Subgroup (Perm (Fin 3))} (hK : IsPGroup 2 K) (hN : ∀ k ∈ K, ξ * k * ξ⁻¹ ∈ K) :
    ∀ k ∈ K, k = 1 := by
  intro k hk
  by_contra hk1
  obtain ⟨i, j, hw3, hw1⟩ := fact_three ξ k h3 h1 hk1
  exact hw1 (eq_one_of_conj_mul hK hN hk i j hw3)

theorem isKlein4_of_normalized_four {ξ : Perm (Fin 4)} (h3 : ξ ^ 3 = 1) (h1 : ξ ≠ 1)
    {K : Subgroup (Perm (Fin 4))} (hK : IsPGroup 2 K) (hN : ∀ k ∈ K, ξ * k * ξ⁻¹ ∈ K) :
    ∀ k ∈ K, IsKlein4 k := by
  intro k hk
  by_contra hk1
  obtain ⟨i, j, hw3, hw1⟩ := fact_four ξ k h3 h1 hk1
  exact hw1 (eq_one_of_conj_mul hK hN hk i j hw3)

theorem exists_conj_eq_four {ξ : Perm (Fin 4)} (h3 : ξ ^ 3 = 1) (h1 : ξ ≠ 1)
    {v w : Perm (Fin 4)} (hv : IsKlein4 v) (hv1 : v ≠ 1) (hw : IsKlein4 w) (hw1 : w ≠ 1) :
    ∃ j : ℕ, ξ ^ j * v * (ξ ^ j)⁻¹ = w := by
  obtain ⟨j, hj⟩ := fact_orbit ξ v w h3 h1 hv hv1 hw hw1
  exact ⟨j.val, hj⟩

end CFSG.Quasithin.Fan86
