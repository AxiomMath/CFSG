module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix

section ConjN

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem glnInv_mul (P : GL ι F) :
    ((P⁻¹ : GL ι F) : Matrix ι ι F) * (P : Matrix ι ι F) = 1 :=
  Units.inv_mul P

theorem mul_glnInv (P : GL ι F) :
    (P : Matrix ι ι F) * ((P⁻¹ : GL ι F) : Matrix ι ι F) = 1 :=
  Units.mul_inv P

theorem conjN_mul_aux (Pm Pi X Y : Matrix ι ι F) (h : Pi * Pm = 1) :
    Pm * (X * Y) * Pi = (Pm * X * Pi) * (Pm * Y * Pi) := by
  symm
  calc (Pm * X * Pi) * (Pm * Y * Pi) = Pm * X * (Pi * Pm) * Y * Pi := by
        simp only [Matrix.mul_assoc]
    _ = Pm * (X * Y) * Pi := by
        rw [h, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem conjN_conj_aux (Pm Pi X : Matrix ι ι F) (h : Pi * Pm = 1) :
    Pi * (Pm * X * Pi) * Pm = X := by
  calc Pi * (Pm * X * Pi) * Pm = (Pi * Pm) * X * (Pi * Pm) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [h, Matrix.one_mul, Matrix.mul_one]

@[expose] def conjSLn (P : GL ι F) :
    Matrix.SpecialLinearGroup ι F →* Matrix.SpecialLinearGroup ι F where
  toFun x := ⟨(P : Matrix ι ι F) * (x : Matrix ι ι F) * ((P⁻¹ : GL ι F) : Matrix ι ι F), by
    rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, mul_glnInv,
      Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    show (P : Matrix ι ι F) * (1 : Matrix ι ι F) * ((P⁻¹ : GL ι F) : Matrix ι ι F) = 1
    rw [Matrix.mul_one, mul_glnInv]
  map_mul' x y := Subtype.ext (conjN_mul_aux _ _ _ _ (glnInv_mul P))

theorem coe_conjSLn (P : GL ι F) (x : Matrix.SpecialLinearGroup ι F) :
    ((conjSLn P x : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) =
      (P : Matrix ι ι F) * (x : Matrix ι ι F) * ((P⁻¹ : GL ι F) : Matrix ι ι F) :=
  rfl

theorem conjSLn_inv_conjSLn (P : GL ι F) (x : Matrix.SpecialLinearGroup ι F) :
    conjSLn P⁻¹ (conjSLn P x) = x := by
  apply Subtype.ext
  rw [coe_conjSLn, coe_conjSLn, inv_inv]
  exact conjN_conj_aux _ _ _ (glnInv_mul P)

@[expose] def conjSLnEquiv (P : GL ι F) :
    Matrix.SpecialLinearGroup ι F ≃* Matrix.SpecialLinearGroup ι F where
  toFun := conjSLn P
  invFun := conjSLn P⁻¹
  left_inv x := conjSLn_inv_conjSLn P x
  right_inv x := by
    have := conjSLn_inv_conjSLn P⁻¹ x
    rwa [inv_inv] at this
  map_mul' := map_mul (conjSLn P)

theorem conjSLnEquiv_eq_of_mul_eq (P : GL ι F) {u g : Matrix.SpecialLinearGroup ι F}
    (h : (P : Matrix ι ι F) * (u : Matrix ι ι F) = (g : Matrix ι ι F) * (P : Matrix ι ι F)) :
    conjSLnEquiv P u = g := by
  apply Subtype.ext
  show (P : Matrix ι ι F) * (u : Matrix ι ι F) * ((P⁻¹ : GL ι F) : Matrix ι ι F) = _
  rw [h, Matrix.mul_assoc, mul_glnInv, Matrix.mul_one]

end ConjN

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
