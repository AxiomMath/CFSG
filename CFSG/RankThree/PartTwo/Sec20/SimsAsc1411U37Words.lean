module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix

variable {K : Type} [Field K]

theorem map_fin_three_of {L : Type*} (φ : K → L) (a b c d e f g h i : K) :
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) K).map φ =
      !![φ a, φ b, φ c; φ d, φ e, φ f; φ g, φ h, φ i] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def u37Y (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![2 - z, 1 - z, -2 * z; 1 - z, 2, 3 + z; -2 * z, 3 + z, 0]

@[expose] def u37YBar (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![2 + z, 1 + z, 2 * z; 1 + z, 2, 3 - z; 2 * z, 3 - z, 0]

theorem transpose_u37Y (z : K) : (u37Y z)ᵀ = u37Y z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem transpose_u37YBar (z : K) : (u37YBar z)ᵀ = u37YBar z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem map_u37Y (σ : K →+* K) {z : K} (hσ : σ z = -z) : (u37Y z).map σ = u37YBar z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37Y, u37YBar, hσ, map_ofNat] <;> ring

variable {z : K}

theorem u37YBar_mul_u37Y (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37YBar z * u37Y z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37Y, u37YBar, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

theorem u37Y_mul_u37YBar (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37Y z * u37YBar z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37Y, u37YBar, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

theorem det_u37Y (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : (u37Y z).det = 1 := by
  simp [u37Y, Matrix.det_fin_three]
  grind

theorem u37Y_pow_fortyTwo (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37Y z ^ 42 = u37YBar z := by
  have e2 : u37Y z ^ 2 =
      !![2 + z, 1 + 3 * z, -1 + z; 1 + 3 * z, -1 - 3 * z, -2; -1 + z, -2, 3 - z] := by
    rw [sq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u37Y, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e4 : u37Y z ^ 4 =
      !![-3 + z, -1 - z, -z; -1 - z, -3 - 2 * z, -3 - z; -z, -3 - z, -1 - z] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e8 : u37Y z ^ 8 =
      !![-2 + 3 * z, -2 + 3 * z, -1 + z; -2 + 3 * z, 2 - z, 3; -1 + z, 3, -2 + z] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e16 : u37Y z ^ 16 = !![3 + 2 * z, 1 - z, 3 + z; 1 - z, -2 - 2 * z, -3 + 2 * z;
      3 + z, -3 + 2 * z, -1 + z] := by
    rw [show 16 = 8 + 8 from rfl, pow_add, e8]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e32 : u37Y z ^ 32 = !![2 + 2 * z, -2 + 2 * z, -1 + 2 * z; -2 + 2 * z, -1 + z, 3 + 2 * z;
      -1 + 2 * z, 3 + 2 * z, 2 - z] := by
    rw [show 32 = 16 + 16 from rfl, pow_add, e16]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e40 : u37Y z ^ 40 =
      !![1 + 3 * z, 1, -1 + z; 1, -2 - z, -2 - 2 * z; -1 + z, -2 - 2 * z, 2] := by
    rw [show 40 = 32 + 8 from rfl, pow_add, e32, e8]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  rw [show 42 = 40 + 2 from rfl, pow_add, e40, e2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37YBar, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem u37Y_pow_fortyThree (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37Y z ^ 43 = 1 := by
  rw [pow_succ, u37Y_pow_fortyTwo h7 hz, u37YBar_mul_u37Y h7 hz]

theorem u37Y_zero_one_ne_zero (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37Y z 0 1 ≠ 0 := by
  simp only [u37Y, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  intro h
  exact one_ne_zero (α := K) (by linear_combination h7 + 3 * hz + 3 * (z + 1) * h)

@[expose] def u37T : Matrix (Fin 3) (Fin 3) K := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

@[expose] def u37C₁ : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

@[expose] def u37C₂ : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

@[expose] def u37C₃ (z : K) : Matrix (Fin 3) (Fin 3) K := !![2, 0, -z; 0, -1, 0; z, 0, -2]

@[expose] def u37W (z : K) : Matrix (Fin 3) (Fin 3) K := !![z, 0, -2; 2, 0, -z; 0, -1, 0]

@[expose] def u37WInv (z : K) : Matrix (Fin 3) (Fin 3) K := !![-z, 2, 0; 0, 0, -1; -2, z, 0]

theorem map_u37C₁ (σ : K →+* K) : (u37C₁ : Matrix (Fin 3) (Fin 3) K).map σ = u37C₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37C₁]

theorem map_u37C₂ (σ : K →+* K) : (u37C₂ : Matrix (Fin 3) (Fin 3) K).map σ = u37C₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37C₂]

theorem map_u37C₃ (σ : K →+* K) (hσ : σ z = -z) : (u37C₃ z).map σ = (u37C₃ z)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37C₃, hσ, map_ofNat]

theorem map_u37W (σ : K →+* K) (hσ : σ z = -z) : ((u37W z).map σ)ᵀ = u37WInv z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37W, u37WInv, hσ, map_ofNat]

theorem transpose_u37C₁ : (u37C₁ : Matrix (Fin 3) (Fin 3) K)ᵀ = u37C₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem transpose_u37C₂ : (u37C₂ : Matrix (Fin 3) (Fin 3) K)ᵀ = u37C₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem u37C₁_mul_self : (u37C₁ : Matrix (Fin 3) (Fin 3) K) * u37C₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37C₁, Matrix.mul_apply, Fin.sum_univ_three]

theorem u37C₂_mul_self : (u37C₂ : Matrix (Fin 3) (Fin 3) K) * u37C₂ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37C₂, Matrix.mul_apply, Fin.sum_univ_three]

theorem u37C₃_mul_self (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37C₃ z * u37C₃ z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37C₃, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem det_u37C₁ : (u37C₁ : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [u37C₁, Matrix.det_fin_three]

theorem det_u37C₂ : (u37C₂ : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [u37C₂, Matrix.det_fin_three]

theorem det_u37C₃ (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : (u37C₃ z).det = 1 := by
  simp [u37C₃, Matrix.det_fin_three]
  grind

theorem det_u37W (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : (u37W z).det = 1 := by
  simp [u37W, Matrix.det_fin_three]
  grind

theorem u37WInv_mul_u37W (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37WInv z * u37W z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37W, u37WInv, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

theorem u37W_mul_u37WInv (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37W z * u37WInv z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37W, u37WInv, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

theorem u37T_mul_u37C : u37T * u37C₁ * u37C₂ * u37C₃ z = u37W z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u37T, u37C₁, u37C₂, u37C₃, u37W, Matrix.mul_apply, Fin.sum_univ_three]

theorem u37W_pow_fortyTwo (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37W z ^ 42 = u37WInv z := by
  have e2 : u37W z ^ 2 = !![3, 2, -2 * z; 2 * z, z, 3; -2, 0, z] := by
    rw [sq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u37W, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e4 : u37W z ^ 4 =
      !![2 + z, -1 + 2 * z, z; -z, 3 - 3 * z, 2 - z; 1 - 2 * z, 3, 3 - 3 * z] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e8 : u37W z ^ 8 =
      !![2 - z, -3 + z, 3 * z; -3 * z, 1 + z, -1 + 3 * z; 3 - z, -2, 1 + z] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e16 : u37W z ^ 16 = !![3, -2 - 3 * z, -2 - z; 2 + z, -3 - 2 * z, 3 - 3 * z;
      2 + 3 * z, -2 + 2 * z, -3 - 2 * z] := by
    rw [show 16 = 8 + 8 from rfl, pow_add, e8]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e32 : u37W z ^ 32 = !![-3 - 2 * z, 2 + 2 * z, -1 + z; 1 - z, -2 + 2 * z, -3 + 2 * z;
      -2 - 2 * z, -1 - 2 * z, -2 + 2 * z] := by
    rw [show 32 = 16 + 16 from rfl, pow_add, e16]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e40 : u37W z ^ 40 = !![-3 - 3 * z, -1 - 2 * z, 2 * z; -2 * z, -3, z;
      1 + 2 * z, -3 - 3 * z, -3] := by
    rw [show 40 = 32 + 8 from rfl, pow_add, e32, e8]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  rw [show 42 = 40 + 2 from rfl, pow_add, e40, e2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u37WInv, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem u37W_pow_fortyThree (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : u37W z ^ 43 = 1 := by
  rw [pow_succ, u37W_pow_fortyTwo h7 hz, u37WInv_mul_u37W h7 hz]

theorem u37W_zero_zero_ne (hz : z ^ 2 = 3) (h3 : (3 : K) ≠ 0) : u37W z 0 0 ≠ u37W z 1 1 := by
  simp only [u37W, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rintro rfl
  exact h3 (by rw [← hz]; ring)

end CFSG.RankThree.PartTwo.Sec20
