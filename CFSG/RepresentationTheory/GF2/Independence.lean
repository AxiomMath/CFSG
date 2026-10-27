module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.RepresentationTheory.GF2

variable {F : Type*} [Field F]

theorem mulVec_injective_of_mul_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι F} (h : B * A = 1) : Function.Injective A.mulVec := by
  intro x y hxy
  have h1 : A.mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have h2 : x - y = B.mulVec (A.mulVec (x - y)) := by
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  rw [h1, Matrix.mulVec_zero] at h2
  exact sub_eq_zero.mp h2

end CFSG.RepresentationTheory.GF2

