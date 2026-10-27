module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open Matrix

section SymForm

variable {F : Type} [Field F]

theorem exists_add_sq_eq [Fintype F] (hodd : Fintype.card F % 2 = 1) {a b : F} (ha : a ≠ 0)
    (hb : b ≠ 0) (c : F) : ∃ x y : F, a * x ^ 2 + b * y ^ 2 = c := by
  have hf : (Polynomial.C a * Polynomial.X ^ 2).degree = 2 := by
    rw [Polynomial.degree_C_mul_X_pow 2 ha]; rfl
  have hg : (Polynomial.C b * Polynomial.X ^ 2 - Polynomial.C c).degree = 2 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
      rw [Polynomial.degree_C_mul_X_pow 2 hb]
    · rfl
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨x, y, ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub] at h
  linear_combination h

theorem exists_congr_diagonal (h2 : (2 : F) ≠ 0) (B : Matrix (Fin 3) (Fin 3) F) (hB : Bᵀ = B)
    (hdet : B.det ≠ 0) :
    ∃ (P : Matrix (Fin 3) (Fin 3) F) (d : Fin 3 → F), P.det ≠ 0 ∧ (∀ i, d i ≠ 0) ∧
      Pᵀ * B * P = Matrix.diagonal d := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hsymm : LinearMap.IsSymm (Matrix.toBilin' B) := by
    refine ⟨fun x y => ?_⟩
    change (Matrix.toBilin' B) x y = (Matrix.toBilin' B) y x
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hB, dotProduct_comm]
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  have hfr : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  set w := v.reindex (finCongr hfr) with hw
  have hwo : ∀ i j, i ≠ j → Matrix.toBilin' B (w i) (w j) = 0 := by
    intro i j hij
    rw [hw, Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    exact hv (fun h => hij (by simpa using congrArg (finCongr hfr) h))
  have hnd : (Matrix.toBilin' B).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  have hwd : ∀ i, Matrix.toBilin' B (w i) (w i) ≠ 0 := by
    have hwo' : LinearMap.IsOrthoᵢ (Matrix.toBilin' B) w := fun i j hij => hwo i j hij
    exact LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate hwo' hnd
  set P := (Pi.basisFun F (Fin 3)).toMatrix w with hP
  have hPij : ∀ i j, P i j = w j i := fun i j => by
    rw [hP, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  refine ⟨P, fun i => Matrix.toBilin' B (w i) (w i), ?_, hwd, ?_⟩
  · rw [hP, ← Module.Basis.det_apply]
    exact ((Pi.basisFun F (Fin 3)).isUnit_det w).ne_zero
  · ext i j
    have e : (Pᵀ * B * P) i j = Matrix.toBilin' B (w i) (w j) := by
      rw [Matrix.toBilin'_apply', Matrix.mul_apply]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hPij, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hwo i j hij]

@[expose] def moveZeroOne (a b x y : F) : Matrix (Fin 3) (Fin 3) F :=
  !![x, -b * y, 0; y, a * x, 0; 0, 0, 1]

@[expose] def moveOneTwo (a b x y : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, x, -b * y; 0, y, a * x]

theorem moveZeroOne_conj (a b e x y : F) :
    (moveZeroOne a b x y)ᵀ * Matrix.diagonal ![a, b, e] * moveZeroOne a b x y =
      Matrix.diagonal ![a * x ^ 2 + b * y ^ 2, a * b * (a * x ^ 2 + b * y ^ 2), e] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [moveZeroOne, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;> ring

theorem moveOneTwo_conj (a b e x y : F) :
    (moveOneTwo a b x y)ᵀ * Matrix.diagonal ![e, a, b] * moveOneTwo a b x y =
      Matrix.diagonal ![e, a * x ^ 2 + b * y ^ 2, a * b * (a * x ^ 2 + b * y ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [moveOneTwo, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;> ring

theorem det_moveZeroOne (a b x y : F) : (moveZeroOne a b x y).det = a * x ^ 2 + b * y ^ 2 := by
  simp [moveZeroOne, Matrix.det_fin_three]; ring

theorem det_moveOneTwo (a b x y : F) : (moveOneTwo a b x y).det = a * x ^ 2 + b * y ^ 2 := by
  simp [moveOneTwo, Matrix.det_fin_three]; ring

theorem exists_eq_smul_mul_transpose [Finite F] (h2 : (2 : F) ≠ 0)
    (B : Matrix (Fin 3) (Fin 3) F) (hB : Bᵀ = B) (hdet : B.det ≠ 0) :
    ∃ (c : F) (h : Matrix (Fin 3) (Fin 3) F), c ≠ 0 ∧ h.det ≠ 0 ∧ B = c • (h * hᵀ) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hodd : Fintype.card F % 2 = 1 := by
    refine FiniteField.odd_card_of_char_ne_two fun hc => h2 ?_
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [hc] at this
    exact_mod_cast this
  obtain ⟨P, d, hP, hd, hPB⟩ := exists_congr_diagonal h2 B hB hdet
  set lam := d 0 * d 1 * d 2 with hlam
  have hlam0 : lam ≠ 0 := mul_ne_zero (mul_ne_zero (hd 0) (hd 1)) (hd 2)
  obtain ⟨x, y, hxy⟩ := exists_add_sq_eq hodd (hd 0) (hd 1) lam
  obtain ⟨x', y', hxy'⟩ := exists_add_sq_eq hodd
    (mul_ne_zero (mul_ne_zero (hd 0) (hd 1)) hlam0) (hd 2) lam
  set R₁ := moveZeroOne (d 0) (d 1) x y
  set R₂ := moveOneTwo (d 0 * d 1 * lam) (d 2) x' y'
  set R₃ : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, 1, lam⁻¹]
  have hD : Matrix.diagonal d = Matrix.diagonal ![d 0, d 1, d 2] := by
    congr 1; funext i; fin_cases i <;> rfl
  have h1 : R₁ᵀ * Matrix.diagonal d * R₁ = Matrix.diagonal ![lam, d 0 * d 1 * lam, d 2] := by
    rw [hD, moveZeroOne_conj, hxy]
  have h2' : R₂ᵀ * Matrix.diagonal ![lam, d 0 * d 1 * lam, d 2] * R₂ =
      Matrix.diagonal ![lam, lam, lam ^ 3] := by
    rw [moveOneTwo_conj, hxy']
    congr 1
    ext i
    fin_cases i <;> simp [hlam]
    all_goals ring
  have h3 : R₃ᵀ * Matrix.diagonal ![lam, lam, lam ^ 3] * R₃ =
      lam • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
    all_goals field_simp
  set Q := P * R₁ * R₂ * R₃ with hQ
  have hQB : Qᵀ * B * Q = lam • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [hQ]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← h3, ← h2', ← h1, ← hPB]
    simp only [Matrix.mul_assoc]
  have hQdet : Q.det ≠ 0 := by
    rw [hQ, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_moveZeroOne, det_moveOneTwo,
      hxy, hxy']
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hP hlam0) hlam0) ?_
    simp [R₃, Matrix.det_diagonal, Fin.prod_univ_three, hlam0]
  have hQu : IsUnit Q.det := hQdet.isUnit
  refine ⟨lam, (Q⁻¹)ᵀ, hlam0, ?_, ?_⟩
  · rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hQdet
  · have hQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
    calc B = (Q * Q⁻¹)ᵀ * B * (Q * Q⁻¹) := by
          rw [hQi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (Q⁻¹)ᵀ * (Qᵀ * B * Q) * Q⁻¹ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (Q⁻¹)ᵀ * (lam • (1 : Matrix (Fin 3) (Fin 3) F)) * Q⁻¹ := by rw [hQB]
      _ = lam • ((Q⁻¹)ᵀ * ((Q⁻¹)ᵀ)ᵀ) := by
          rw [Matrix.transpose_transpose, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

end SymForm

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
