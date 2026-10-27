module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

namespace CFSG
end CFSG
open CFSG

/-!
# Concrete split-torus matrices in SL(2,F)

Finite `2 × 2` case splits live here, outside the large group-theoretic proof
of the split-torus normalizer theorem.
-/

namespace CFSG.Glauberman
namespace Dickson

universe u

/-- The standard diagonal copy of `Fˣ` in `SL(2,F)`. -/
@[expose] public def splitTorusSLHom (F : Type u) [Field F] :
    Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
  { toFun := fun a => ⟨!![(a : F), 0; 0, (a⁻¹ : F)], by
      simp [Matrix.det_fin_two]⟩
    map_one' := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      ext i j
      change (!![(↑(a * b) : F), 0; 0, (↑(a * b) : F)⁻¹] :
          Matrix (Fin 2) (Fin 2) F) i j =
        ((!![(a : F), 0; 0, (a⁻¹ : F)] : Matrix (Fin 2) (Fin 2) F) *
          (!![(b : F), 0; 0, (b⁻¹ : F)] : Matrix (Fin 2) (Fin 2) F)) i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm] }

@[simp] public theorem splitTorusSLHom_coe
    {F : Type u} [Field F] (a : Fˣ) :
    (splitTorusSLHom F a : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), 0; 0, (a⁻¹ : F)] := rfl

/-- A split-torus matrix whose two diagonal entries agree is scalar. -/
public theorem splitTorusSLHom_eq_scalar_of_val_eq_inv
    {F : Type u} [Field F] (a : Fˣ)
    (ha : (a : F) = (a⁻¹ : F)) :
    Matrix.scalar (Fin 2) (a : F) =
      (splitTorusSLHom F a : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · exact ha

/-- The standard Weyl reflection in `SL(2,F)`. -/
@[expose] public def standardSplitWeylSL (F : Type u) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

@[simp] public theorem standardSplitWeylSL_coe
    (F : Type u) [Field F] :
    (standardSplitWeylSL F : Matrix (Fin 2) (Fin 2) F) =
      !![0, -1; 1, 0] := rfl

/-- The inverse of the standard Weyl reflection. -/
public theorem standardSplitWeylSL_inv
    (F : Type u) [Field F] :
    (standardSplitWeylSL F)⁻¹ =
      (⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [standardSplitWeylSL, Matrix.adjugate_fin_two]

/-- The standard Weyl reflection inverts the standard split torus. -/
public theorem standardSplitWeylSL_conj
    {F : Type u} [Field F] (a : Fˣ) :
    standardSplitWeylSL F * splitTorusSLHom F a *
        (standardSplitWeylSL F)⁻¹ =
      splitTorusSLHom F a⁻¹ := by
  rw [standardSplitWeylSL_inv]
  apply Subtype.ext
  change ((standardSplitWeylSL F : Matrix (Fin 2) (Fin 2) F) *
      (splitTorusSLHom F a : Matrix (Fin 2) (Fin 2) F) *
        ((⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ :
          Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
    (splitTorusSLHom F a⁻¹ : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardSplitWeylSL_coe, splitTorusSLHom_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The square of the standard Weyl reflection is central. -/
public theorem standardSplitWeylSL_sq_mem_center
    (F : Type u) [Field F] :
    standardSplitWeylSL F * standardSplitWeylSL F ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  change Matrix.scalar (Fin 2) (-1 : F) =
    ((standardSplitWeylSL F : Matrix (Fin 2) (Fin 2) F) *
      (standardSplitWeylSL F : Matrix (Fin 2) (Fin 2) F))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardSplitWeylSL, Matrix.mul_apply, Fin.sum_univ_two]

/-- A diagonal element of `SL(2,F)` belongs to the standard split torus. -/
public theorem eq_splitTorusSLHom_of_offDiagonal_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    ∃ u : Fˣ, A = splitTorusSLHom F u := by
  have hdet := A.property
  rw [Matrix.det_fin_two, h01, h10, zero_mul, sub_zero] at hdet
  have hA00 : A 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  let u : Fˣ := Units.mk0 (A 0 0) hA00
  have hA11 : A 1 1 = (A 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  refine ⟨u, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusSLHom_coe, u, h01, h10, hA11]

/-- An antidiagonal element of `SL(2,F)` is a Weyl reflection times a
standard split-torus element. -/
public theorem eq_standardSplitWeylSL_mul_splitTorusSLHom_of_diagonal_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h00 : A 0 0 = 0) (h11 : A 1 1 = 0) :
    ∃ u : Fˣ, A = standardSplitWeylSL F * splitTorusSLHom F u := by
  have hdet := A.property
  rw [Matrix.det_fin_two, h00, h11, zero_mul, zero_sub] at hdet
  have hA10 : A 1 0 ≠ 0 := by
    intro h
    rw [h, mul_zero, neg_zero] at hdet
    exact zero_ne_one hdet
  let u : Fˣ := Units.mk0 (A 1 0) hA10
  have hnegprod : (-A 0 1) * A 1 0 = 1 := by
    simpa using hdet
  have hneg : -A 0 1 = (A 1 0)⁻¹ :=
    eq_inv_of_mul_eq_one_left hnegprod
  have hA01 : A 0 1 = -(A 1 0)⁻¹ := by
    calc
      A 0 1 = -(-A 0 1) := by simp
      _ = -(A 1 0)⁻¹ := congrArg Neg.neg hneg
  refine ⟨u, ?_⟩
  apply Subtype.ext
  ext i j
  change (A : Matrix (Fin 2) (Fin 2) F) i j =
    ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) *
      !![(u : F), 0; 0, (u⁻¹ : F)]) i j
  fin_cases i <;> fin_cases j <;>
    simp [u, Matrix.mul_apply, Fin.sum_univ_two, h00, h11, hA01]

/-- A diagonal matrix commutes with the standard split torus. -/
public theorem mul_splitTorusSLHom_eq_splitTorusSLHom_mul_of_offDiagonal_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) (c : Fˣ) :
    A * splitTorusSLHom F c = splitTorusSLHom F c * A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusSLHom_coe, Matrix.mul_apply, Fin.sum_univ_two,
      h01, h10, mul_comm]

/-- An antidiagonal matrix intertwines a split-torus element with its inverse. -/
public theorem mul_splitTorusSLHom_eq_inv_mul_of_diagonal_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h00 : A 0 0 = 0) (h11 : A 1 1 = 0) (c : Fˣ) :
    A * splitTorusSLHom F c = splitTorusSLHom F c⁻¹ * A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusSLHom_coe, Matrix.mul_apply, Fin.sum_univ_two,
      h00, h11, mul_comm]

/-- A matrix intertwining a noncentral split-torus element with another
split-torus element is diagonal or antidiagonal. -/
public theorem split_matrix_diag_or_antidiag
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (a b : Fˣ) (r : F)
    (ha_ne_inv : (a : F) ≠ (a⁻¹ : F))
    (heq :
      !![(b : F), 0; 0, (b⁻¹ : F)] * Matrix.scalar (Fin 2) r *
          (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) *
          !![(a : F), 0; 0, (a⁻¹ : F)]) :
    (A 0 1 = 0 ∧ A 1 0 = 0) ∨
      (A 0 0 = 0 ∧ A 1 1 = 0) := by
  have h00 := congrFun (congrFun heq (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun heq (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun heq (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun heq (1 : Fin 2)) (1 : Fin 2)
  simp [Matrix.mul_apply] at h00 h01 h10 h11
  by_cases hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
  · right
    refine ⟨hA00, ?_⟩
    have hdet := A.property
    rw [Matrix.det_fin_two, hA00, zero_mul, zero_sub] at hdet
    have hA01 : A 0 1 ≠ 0 := by
      intro h
      rw [h, zero_mul, neg_zero] at hdet
      exact zero_ne_one hdet
    have hA10 : A 1 0 ≠ 0 := by
      intro h
      rw [h, mul_zero, neg_zero] at hdet
      exact zero_ne_one hdet
    have hbinvr_a : (b⁻¹ : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA10
      simpa [mul_assoc, mul_comm] using h10
    by_contra hA11
    have hbinvr_ainv : (b⁻¹ : F) * r = (a⁻¹ : F) := by
      apply mul_right_cancel₀ hA11
      simpa [mul_assoc, mul_comm] using h11
    exact ha_ne_inv (hbinvr_a.symm.trans hbinvr_ainv)
  · left
    have hbr_a : (b : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA00
      simpa [mul_assoc, mul_comm] using h00
    have hA01 : A 0 1 = 0 := by
      by_contra hA01
      have hbr_ainv : (b : F) * r = (a⁻¹ : F) := by
        apply mul_right_cancel₀ hA01
        simpa [mul_assoc, mul_comm] using h01
      exact False.elim (ha_ne_inv (hbr_a.symm.trans hbr_ainv))
    refine ⟨hA01, ?_⟩
    have hdet := A.property
    rw [Matrix.det_fin_two, hA01, zero_mul, sub_zero] at hdet
    have hA11 : A 1 1 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdet
      exact zero_ne_one hdet
    have hbinvr_ainv : (b⁻¹ : F) * r = (a⁻¹ : F) := by
      apply mul_right_cancel₀ hA11
      simpa [mul_assoc, mul_comm] using h11
    by_contra hA10
    have hbinvr_a : (b⁻¹ : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA10
      simpa [mul_assoc, mul_comm] using h10
    exact ha_ne_inv (hbinvr_a.symm.trans hbinvr_ainv)

end Dickson
end CFSG.Glauberman
