module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.H.S77

open Matrix

abbrev SL32 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

abbrev Vec : Type := Fin 3 → ZMod 2

abbrev e1 : Vec := ![1, 0, 0]

abbrev e3 : Vec := ![0, 0, 1]

abbrev act (g : SL32) (x : Vec) : Vec := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x

abbrev dact (g : SL32) (y : Vec) : Vec :=
  ((g⁻¹ : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ y

@[expose] def th0 : SL32 := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

abbrev SingDiag (x y : Vec) : Prop := x ≠ 0 ∧ y ≠ 0 ∧ y ⬝ᵥ x = 0

abbrev InVm (w : Vec × Vec) : Prop := w.1 0 = 0 ∧ w.2 0 = 0

theorem dact_eq_iff (g : SL32) (y : Vec) :
    dact g y = y ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ y = y := by
  have hinv : (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
      ((g⁻¹ : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have hinv' : ((g⁻¹ : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [dact, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]

theorem fix_seven : ∀ g : SL32, (g ^ 7 = 1 ∧ g ≠ 1) → ∀ x : Vec, act g x = x → x = 0 := by
  decide +kernel

theorem tfix_seven : ∀ g : SL32, (g ^ 7 = 1 ∧ g ≠ 1) → ∀ y : Vec,
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ y = y → y = 0 := by
  decide +kernel

theorem dfix_seven (g : SL32) (hg : g ^ 7 = 1 ∧ g ≠ 1) (y : Vec) (hy : dact g y = y) : y = 0 :=
  tfix_seven g hg y ((dact_eq_iff g y).mp hy)

end CFSG.Quasithin.H.S77
