module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen

open Matrix

abbrev GL6 : Type := GL (Fin 6) (ZMod 2)

abbrev GL4 : Type := GL (Fin 4) (ZMod 2)

abbrev M6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def U0 : M6 :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

@[expose] def U0sq : M6 :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 0]

theorem U0_mul_U0 : U0 * U0 = U0sq := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U0, U0sq, Matrix.mul_apply, Fin.sum_univ_six] <;> decide

theorem U0_mul_U0sq : U0 * U0sq = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U0, U0sq, Matrix.mul_apply, Fin.sum_univ_six] <;> decide

theorem U0sq_mul_U0 : U0sq * U0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U0, U0sq, Matrix.mul_apply, Fin.sum_univ_six] <;> decide

@[expose] def u0 : GL6 := ⟨U0, U0sq, U0_mul_U0sq, U0sq_mul_U0⟩

theorem coe_u0 : (u0 : M6) = U0 := rfl

theorem u0_sq : u0 * u0 = u0⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_one, coe_u0, U0_mul_U0, U0sq_mul_U0]

theorem u0_pow_three : u0 ^ 3 = 1 := by
  rw [pow_succ, pow_two, u0_sq, inv_mul_cancel]

theorem u0_ne_one : u0 ≠ 1 := by
  intro h
  have e := congrArg (fun g : GL6 => (g : M6) 4 4) h
  simp [coe_u0, U0] at e

theorem orderOf_u0 : orderOf u0 = 3 :=
  orderOf_eq_prime u0_pow_three u0_ne_one

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen
