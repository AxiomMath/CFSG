module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBN

open Matrix

variable {R : Type*} [CommRing R] {K : Type*} [Field K]

@[expose] def symBasis : Fin 6 → Matrix (Fin 3) (Fin 3) R :=
  ![single 2 2 1, -(single 1 2 1 + single 2 1 1), single 0 2 1 + single 2 0 1, single 1 1 1,
    -(single 0 1 1 + single 1 0 1), single 0 0 1]

@[expose] def symCoord : Matrix (Fin 3) (Fin 3) R →ₗ[R] Fin 6 → R where
  toFun X := ![X 2 2, -X 1 2, X 0 2, X 1 1, -X 0 1, X 0 0]
  map_add' X Y := by
    funext k
    fin_cases k <;> simp <;> ring
  map_smul' c X := by
    funext k
    fin_cases k <;> simp

theorem symCoord_apply (X : Matrix (Fin 3) (Fin 3) R) :
    symCoord X = ![X 2 2, -X 1 2, X 0 2, X 1 1, -X 0 1, X 0 0] :=
  rfl

@[expose] def sym2Mat (B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun k l => symCoord (B * symBasis l * Bᵀ) k

theorem sym2Mat_apply (B : Matrix (Fin 3) (Fin 3) R) (k l : Fin 6) :
    sym2Mat B k l = symCoord (B * symBasis l * Bᵀ) k :=
  rfl

theorem sum_symCoord_smul_symBasis {Y : Matrix (Fin 3) (Fin 3) R} (hY : Yᵀ = Y) :
    ∑ m, symCoord Y m • symBasis m = Y := by
  have h10 : Y 1 0 = Y 0 1 := congrFun (congrFun hY 0) 1
  have h20 : Y 2 0 = Y 0 2 := congrFun (congrFun hY 0) 2
  have h21 : Y 2 1 = Y 1 2 := congrFun (congrFun hY 1) 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symCoord_apply, symBasis, Fin.sum_univ_succ, h10, h20, h21]

theorem transpose_symBasis (l : Fin 6) : (symBasis l : Matrix (Fin 3) (Fin 3) R)ᵀ = symBasis l := by
  ext i j
  fin_cases l <;> fin_cases i <;> fin_cases j <;> simp [symBasis]

theorem symCoord_symBasis (k l : Fin 6) :
    symCoord (symBasis l : Matrix (Fin 3) (Fin 3) R) k = if k = l then 1 else 0 := by
  fin_cases k <;> fin_cases l <;> simp [symCoord_apply, symBasis]

theorem sym2Mat_one : sym2Mat (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  ext k l
  rw [sym2Mat_apply, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one, symCoord_symBasis,
    Matrix.one_apply]

theorem sym2Mat_mul (B C : Matrix (Fin 3) (Fin 3) R) :
    sym2Mat (B * C) = sym2Mat B * sym2Mat C := by
  ext k l
  set Y := C * symBasis l * Cᵀ with hYdef
  have hY : Yᵀ = Y := by
    rw [hYdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      transpose_symBasis, Matrix.mul_assoc]
  have e : B * C * symBasis l * (B * C)ᵀ = B * Y * Bᵀ := by
    rw [hYdef, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [sym2Mat_apply, e, ← sum_symCoord_smul_symBasis hY, Matrix.mul_sum, Finset.sum_mul, map_sum,
    Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

@[expose] def symPolar (p q : Fin 3) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun k l => symCoord (single p q 1 * symBasis l + symBasis l * single q p 1) k

@[expose] def symQuad (p q : Fin 3) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun k l => symCoord (single p q 1 * symBasis l * single q p 1) k

theorem sym2Mat_one_add_single (p q : Fin 3) (d : R) :
    sym2Mat (1 + single p q d) = 1 + d • symPolar p q + d ^ 2 • symQuad p q := by
  ext k l
  have hD : (single p q d : Matrix (Fin 3) (Fin 3) R) = d • single p q 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hD' : (single q p d : Matrix (Fin 3) (Fin 3) R) = d • single q p 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have e : (1 + single p q d : Matrix (Fin 3) (Fin 3) R) * symBasis l * (1 + single p q d)ᵀ =
      symBasis l + d • (single p q 1 * symBasis l + symBasis l * single q p 1) +
        d ^ 2 • (single p q 1 * symBasis l * single q p 1) := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single, hD, hD']
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul, pow_two]
    abel
  rw [sym2Mat_apply, e, map_add, map_add, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, symCoord_symBasis, Matrix.add_apply,
    Matrix.one_apply, Matrix.smul_apply, symPolar, symQuad, Matrix.of_apply]

theorem symCoord_map {S : Type*} [CommRing S] (f : R →+* S) (X : Matrix (Fin 3) (Fin 3) R)
    (k : Fin 6) : symCoord (X.map f) k = f (symCoord X k) := by
  fin_cases k <;> simp [symCoord_apply]

theorem symBasis_map {S : Type*} [CommRing S] (f : R →+* S) (l : Fin 6) :
    (symBasis l : Matrix (Fin 3) (Fin 3) R).map f = symBasis l := by
  ext i j
  fin_cases l <;> fin_cases i <;> fin_cases j <;> simp [symBasis]

theorem single_one_map {S : Type*} [CommRing S] (f : R →+* S) (p q : Fin 3) :
    (single p q (1 : R)).map f = single p q (1 : S) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem symPolar_map {S : Type*} [CommRing S] (f : R →+* S) (p q : Fin 3) :
    (symPolar p q : Matrix (Fin 6) (Fin 6) R).map f = symPolar p q := by
  ext k l
  rw [Matrix.map_apply, symPolar, symPolar, Matrix.of_apply, Matrix.of_apply, ← symCoord_map,
    Matrix.map_add f (map_add f), Matrix.map_mul, Matrix.map_mul, single_one_map, single_one_map,
    symBasis_map]

theorem symQuad_map {S : Type*} [CommRing S] (f : R →+* S) (p q : Fin 3) :
    (symQuad p q : Matrix (Fin 6) (Fin 6) R).map f = symQuad p q := by
  ext k l
  rw [Matrix.map_apply, symQuad, symQuad, Matrix.of_apply, Matrix.of_apply, ← symCoord_map,
    Matrix.map_mul, Matrix.map_mul, single_one_map, single_one_map, symBasis_map]

@[expose] def symRep : Matrix.SpecialLinearGroup (Fin 3) K →* Matrix (Fin 6) (Fin 6) K where
  toFun A := sym2Mat ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ
  map_one' := by
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, sym2Mat_one]
  map_mul' A B := by
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, sym2Mat_mul]

theorem symRep_apply (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    symRep A = sym2Mat ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ :=
  rfl

theorem eq_one_of_sym2Mat_eq_one {B : Matrix (Fin 3) (Fin 3) K} (h : sym2Mat B = 1)
    (hdet : B.det = 1) : B = 1 := by
  have e : ∀ k l, sym2Mat B k l = (1 : Matrix (Fin 6) (Fin 6) K) k l := fun k l => by rw [h]
  have e05 := e 0 5
  have e35 := e 3 5
  have e55 := e 5 5
  have e03 := e 0 3
  have e53 := e 5 3
  have e33 := e 3 3
  have e30 := e 3 0
  have e50 := e 5 0
  have e00 := e 0 0
  have e44 := e 4 4
  have e22 := e 2 2
  have e11 := e 1 1
  simp only [sym2Mat_apply, symCoord_apply, symBasis, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.transpose_apply, Matrix.one_apply] at e05 e35 e55 e03 e53 e33
  simp only [sym2Mat_apply, symCoord_apply, symBasis, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.transpose_apply, Matrix.one_apply] at e30 e50 e00 e44 e22 e11
  norm_num at e05 e35 e55 e03 e53 e33 e30 e50 e00 e44 e22 e11
  have b20 : B 2 0 = 0 := by simpa using e05
  have b10 : B 1 0 = 0 := by simpa using e35
  have b21 : B 2 1 = 0 := by simpa using e03
  have b01 : B 0 1 = 0 := by simpa using e53
  have b12 : B 1 2 = 0 := by simpa using e30
  have b02 : B 0 2 = 0 := by simpa using e50
  rw [Matrix.det_fin_three, b20, b10, b21, b01, b12, b02] at hdet
  rw [b10, b01] at e44
  rw [b20, b02] at e22
  rw [b21, b12] at e11
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_add] at e44 e22 e11 hdet
  have h00 : B 0 0 = 1 := by
    have h1 : B 0 0 * B 1 1 = 1 := by linear_combination e44
    have h2 : B 0 0 * B 2 2 = 1 := by linear_combination e22
    have h3 : B 0 0 * B 0 0 = 1 := by linear_combination e55
    have hb1 : B 1 1 = B 0 0 := by linear_combination (-B 1 1) * h3 + B 0 0 * h1
    have hb2 : B 2 2 = B 0 0 := by linear_combination (-B 2 2) * h3 + B 0 0 * h2
    rw [hb1, hb2] at hdet
    linear_combination hdet - B 0 0 * h3
  have h11 : B 1 1 = 1 := by linear_combination e44 - B 1 1 * h00
  have h22 : B 2 2 = 1 := by linear_combination e22 - B 2 2 * h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, b20, b10, b21, b01, b12, b02]

theorem symRep_injective : Function.Injective (symRep (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hB := eq_one_of_sym2Mat_eq_one hA (by
    rw [Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe])
  have h1 : (A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) = 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_one, ← Matrix.transpose_transpose
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hB,
      Matrix.transpose_one]
  rw [← inv_inv A, h1, inv_one]

end CFSG.RankThree.Chevalley.SteinbergBN
