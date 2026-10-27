module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.C124.YL.H6

open Matrix

variable {K : Type} [Field K]

theorem exists_dot_one {v : Fin 3 → K} (hv : v ≠ 0) : ∃ y : Fin 3 → K, v ⬝ᵥ y = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  refine ⟨(v i)⁻¹ • Pi.single i 1, ?_⟩
  simp [dotProduct_smul, dotProduct_single, hi]

theorem eq_one_add_vecMulVec {v : Fin 3 → K} (hv : v ≠ 0) {x : Matrix (Fin 3) (Fin 3) K}
    (hx : ∀ y, v ⬝ᵥ y = 0 → x.mulVec y = y) :
    ∃ u : Fin 3 → K, x = 1 + Matrix.vecMulVec u v := by
  obtain ⟨y0, hy0⟩ := exists_dot_one hv
  refine ⟨x.mulVec y0 - y0, ?_⟩
  have key : ∀ y, x.mulVec y = y + (v ⬝ᵥ y) • (x.mulVec y0 - y0) := by
    intro y
    have h1 : v ⬝ᵥ (y - (v ⬝ᵥ y) • y0) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, hy0]
      simp
    have h2 := hx _ h1
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul] at h2
    linear_combination (norm := module) h2
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simp at this
  simp [Matrix.vecMulVec_apply, Matrix.one_apply]
  rw [this, Pi.single_apply]
  ring

theorem dot_eq_zero_of_det {v u : Fin 3 → K} {x : Matrix (Fin 3) (Fin 3) K}
    (hx : x = 1 + Matrix.vecMulVec u v) (hdet : x.det = 1) : v ⬝ᵥ u = 0 := by
  rw [hx, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow] at hdet
  linear_combination hdet

theorem sq_eq_one {v u : Fin 3 → K} (h2 : (2 : K) = 0) (hvu : v ⬝ᵥ u = 0) :
    (1 + Matrix.vecMulVec u v) * (1 + Matrix.vecMulVec u v) = 1 := by
  have h : Matrix.vecMulVec u v + Matrix.vecMulVec u v = 0 := by
    rw [← two_smul K, h2, zero_smul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.vecMulVec_mul_vecMulVec, hvu, zero_smul, Matrix.vecMulVec_zero]
  rw [add_assoc, ← add_assoc (Matrix.vecMulVec u v), h]
  simp

theorem comm_of_same {v u u' : Fin 3 → K} (hvu : v ⬝ᵥ u = 0) (hvu' : v ⬝ᵥ u' = 0) :
    (1 + Matrix.vecMulVec u v) * (1 + Matrix.vecMulVec u' v) =
      (1 + Matrix.vecMulVec u' v) * (1 + Matrix.vecMulVec u v) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.vecMulVec_mul_vecMulVec, hvu, hvu', zero_smul, Matrix.vecMulVec_zero]
  abel



theorem dual_apply_eq_dot (f : (Fin 3 → K) →ₗ[K] K) (y : Fin 3 → K) :
    f y = (fun i => f (Pi.single i 1)) ⬝ᵥ y := by
  conv_lhs => rw [pi_eq_sum_univ y]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem exists_hyperplane [Finite K] (hK : Nat.card K = 4) (W : Submodule K (Fin 3 → K))
    (hW : Nat.card W = 16) : ∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ y, y ∈ W ↔ v ⬝ᵥ y = 0 := by
  have hfr : Module.finrank K W = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := W)
    rw [hW, hK] at h
    have h' : (4 : ℕ) ^ 2 = 4 ^ Module.finrank K W := by rw [← h]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h').symm
  have hlt : W < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, finrank_top, Module.finrank_fin_fun] at hfr
    omega
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hWker : W ≤ LinearMap.ker f := fun y hy => by
    have : f y ∈ W.map f := ⟨y, hy, rfl⟩
    rw [hfW] at this
    exact this
  have hkerfr : Module.finrank K (LinearMap.ker f) = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : Module.finrank K (LinearMap.range f) = 1 := by
      apply le_antisymm
      · simpa using Submodule.finrank_le (LinearMap.range f)
      · apply Submodule.one_le_finrank_iff.2
        intro h
        apply hf0
        refine LinearMap.ext fun y => ?_
        have : f y ∈ LinearMap.range f := ⟨y, rfl⟩
        rw [h] at this
        simpa using this
    rw [h2, Module.finrank_fin_fun] at h1
    omega
  have heq : W = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hWker (by rw [hfr, hkerfr])
  refine ⟨fun i => f (Pi.single i 1), ?_, fun y => ?_⟩
  · intro h
    apply hf0
    refine LinearMap.ext fun y => ?_
    rw [dual_apply_eq_dot f y, h]
    simp
  · rw [heq, LinearMap.mem_ker, dual_apply_eq_dot f y]

end CFSG.Quasithin.C124.YL.H6
