
module

public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Monster.B.TwoA.Sp8.DataBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code

@[expose] def qUpper : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if i < j then gram0 i j else if j = i then (if 6 ≤ (i : ℕ) then 1 else 0)
    else 0

@[expose] def qForm : QuadraticForm (ZMod 2) (Fin 8 → ZMod 2) :=
  (Matrix.toBilin' qUpper).toQuadraticMap

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

theorem qUpper_term (v : Fin 8 → ZMod 2) (i j : Fin 8) :
    v i * qUpper i j * v j = (if i < j then gram0 i j * v i * v j else 0) +
      (if j = i then (if 6 ≤ (i : ℕ) then v i else 0) else 0) := by
  simp only [qUpper, Matrix.of_apply]
  by_cases hij : i < j
  · have hne : j ≠ i := (ne_of_lt hij).symm
    simp only [hij, hne, ite_true, ite_false, add_zero]
    ring
  · by_cases hji : j = i
    · subst hji
      by_cases h6 : 6 ≤ (j : ℕ)
      · simp [h6, zmod2_mul_self]
      · simp [h6]
    · simp [hij, hji]

theorem qForm_apply (v : Fin 8 → ZMod 2) : qForm v = qPoly v := by
  rw [qForm, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply]
  simp_rw [qUpper_term, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [qPoly, add_assoc]
  congr 1
  simp [Fin.sum_univ_eight]

theorem qUpper_add_transpose (i j : Fin 8) : qUpper i j + qUpper j i = gram0 i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem polarBilin_qForm : QuadraticMap.polarBilin qForm = b0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [QuadraticMap.polarBilin_apply_apply, qForm, LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toBilin'_apply, Matrix.toBilin'_apply, b0, Matrix.toBilin'_apply,
    Finset.sum_comm (f := fun i j => y i * qUpper i j * x j), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← qUpper_add_transpose]
  ring

@[expose] def gramInvRows : List ℕ := [194, 65, 56, 52, 44, 28, 3, 1]

@[expose] def gramInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => bvec 8 (gramInvRows.getD i 0) j

theorem gram0_mul_gramInv : gram0 * gramInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem nondegenerate_b0 : b0.Nondegenerate := by
  rw [b0, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
  intro h
  have h1 := congrArg Matrix.det gram0_mul_gramInv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

@[expose] def minusCols : List ℕ := [1, 3, 4, 129, 66, 8, 28, 44]

@[expose] def minusInvCols : List ℕ := [1, 3, 4, 32, 100, 164, 19, 9]

@[expose] def minusP : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun t k => bvec 8 (minusCols.getD k 0) t

@[expose] def minusPinv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun t k => bvec 8 (minusInvCols.getD k 0) t

theorem minusP_mul_minusPinv : minusP * minusPinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem minusPinv_mul_minusP : minusPinv * minusP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def qMinus8 (x : Fin 8 → ZMod 2) : ZMod 2 :=
  x 0 * x 3 + x 1 * x 4 + x 2 * x 5 + x 6 ^ 2 + x 6 * x 7 + x 7 ^ 2

theorem qPoly_minusP : ∀ x : Fin 8 → ZMod 2, qPoly (minusP.mulVec x) = qMinus8 x := by
  decide +kernel

@[expose] def minusCoords8 : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) ≃ Fin 8 where
  toFun
    | .inl i => ⟨i, by omega⟩
    | .inr (.inl i) => ⟨i + 3, by omega⟩
    | .inr (.inr j) => ⟨j + 6, by omega⟩
  invFun := ![.inl 0, .inl 1, .inl 2, .inr (.inl 0), .inr (.inl 1), .inr (.inl 2), .inr (.inr 0),
    .inr (.inr 1)]
  left_inv := by decide
  right_inv := by decide

@[expose] def minusEquiv : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' minusPinv) (Matrix.toLin' minusP)
    (by rw [← Matrix.toLin'_mul, minusPinv_mul_minusP, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, minusP_mul_minusPinv, Matrix.toLin'_one])

theorem quadMinus_funCongr (x : Fin 8 → ZMod 2) :
    CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1 (x ∘ minusCoords8) = qMinus8 x := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply, Fin.sum_univ_three, qMinus8]
  simp only [Function.comp_apply, minusCoords8, Equiv.coe_fn_mk, one_mul]
  rfl

@[expose] def isometryEquivQuadMinus :
    QuadraticMap.IsometryEquiv qForm (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1) :=
  ⟨minusEquiv.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) minusCoords8), fun v => by
    change CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1
      ((minusPinv.mulVec v) ∘ minusCoords8) = qForm v
    rw [quadMinus_funCongr, qForm_apply, ← qPoly_minusP, Matrix.mulVec_mulVec,
      minusP_mul_minusPinv, Matrix.one_mulVec]⟩

theorem equivalent_quadMinus :
    QuadraticMap.Equivalent qForm (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1) :=
  ⟨isometryEquivQuadMinus⟩

theorem card_qPoly_zero :
    (Finset.univ.filter fun v : Fin 8 → ZMod 2 => qPoly v = 0).card = 120 := by
  decide +kernel

end CFSG.Monster.B.TwoA.Sp8
