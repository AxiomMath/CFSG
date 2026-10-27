module

public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType.SporadicShape

open scoped Matrix

theorem exists_fixed_of_nilpotent {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hnil : (A - 1) ^ n = 0) (W : Submodule K (Fin n → K)) (hA : ∀ v ∈ W, v ᵥ* A ∈ W)
    {w : Fin n → K} (hw : w ∈ W) (hw0 : w ≠ 0) :
    ∃ u ∈ W, u ≠ 0 ∧ u ᵥ* A = u := by
  by_contra hcon
  push Not at hcon
  have hN : ∀ v ∈ W, v ᵥ* (A - 1) ∈ W := by
    intro v hv
    rw [sub_eq_add_neg, Matrix.vecMul_add, Matrix.vecMul_neg, Matrix.vecMul_one]
    exact W.add_mem (hA v hv) (W.neg_mem hv)
  have hu : ∀ k : ℕ, w ᵥ* (A - 1) ^ k ∈ W := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul]
      exact hN _ ih
  have hdown : ∀ k : ℕ, k ≤ n → w ᵥ* (A - 1) ^ (n - k) = 0 := by
    intro k
    induction k with
    | zero => intro _; simp [hnil]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 : n - k = (n - (k + 1)) + 1 := by omega
      rw [h2, pow_succ, ← Matrix.vecMul_vecMul] at h1
      set u := w ᵥ* (A - 1) ^ (n - (k + 1)) with hudef
      have hfix : u ᵥ* A = u := by
        have : A = (A - 1) + 1 := by abel
        calc u ᵥ* A = u ᵥ* ((A - 1) + 1) := by rw [← this]
          _ = u ᵥ* (A - 1) + u := by rw [Matrix.vecMul_add, Matrix.vecMul_one]
          _ = u := by rw [h1, zero_add]
      by_contra hne
      exact hcon u (hu _) hne hfix
  exact hw0 (by simpa using hdown n le_rfl)

theorem eq_top_of_spin_rows {K : Type*} [CommRing K] {n : ℕ} (W : Submodule K (Fin n → K))
    (rows : Fin n → Fin n → K) (hrows : ∀ i, rows i ∈ W) (Si : Matrix (Fin n) (Fin n) K)
    (hS : Si * Matrix.of rows = 1) : W = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have e : u = (u ᵥ* Si) ᵥ* Matrix.of rows := by
    rw [Matrix.vecMul_vecMul, hS, Matrix.vecMul_one]
  have e2 : (u ᵥ* Si) ᵥ* Matrix.of rows = ∑ i, (u ᵥ* Si) i • rows i := by
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  rw [e, e2]
  exact Submodule.sum_mem _ fun i _ => W.smul_mem _ (hrows i)

end CFSG.StandardType.SporadicShape
