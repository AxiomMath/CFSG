module

public import CFSG.Quasithin.Recognition.M12AscP2Tab
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

open Subgroup

@[expose] def mGen (i : Fin 4) : ↥ascHModel := ⟨ascHImg i, Subgroup.subset_closure ⟨i, rfl⟩⟩

@[expose] def mZ : ↥ascHModel := mGen 0 * mGen 0

@[expose] def mX : ↥ascHModel := mGen 2

@[expose] def mU : ↥ascHModel := mGen 3

@[expose] def aFPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 6] * List.formPerm [2, 5] * List.formPerm [3, 7] * List.formPerm [9, 10]

theorem aFPerm_mem : aFPerm ∈ ascHModel := (mem_ascHModel_iff _).2 (by decide +kernel)

theorem tabOf_aFPerm : tabOf aFPerm = aFTab := by decide +kernel

@[expose] def mA : ↥ascHModel := ⟨aFPerm, aFPerm_mem⟩

theorem mX_cube : mX * mX * mX = 1 := by decide +kernel
theorem mX_ne : mX ≠ 1 := by decide +kernel
theorem mU_sq : mU * mU = 1 := by decide +kernel
theorem mU_mX : mU * mX * mU = mX⁻¹ := by decide +kernel
theorem mA_sq : mA * mA = 1 := by decide +kernel
theorem mA_ne : mA ≠ 1 := by decide +kernel
theorem cox_local (u' : ↥ascHModel) (mU' : u' = mU ∨ u' = mU * mZ) :
    u' * u' = 1 ∧ u' * mX * u' = mX⁻¹ ∧ (u' * mX) * (u' * mX) = 1 ∧ mA * u' = u' * mA ∧
    mZ * u' = u' * mZ ∧ (mA * u') * (mA * u') = 1 ∧
    (mZ * (mA * u')) * (mZ * (mA * u')) = 1 ∧ (mZ * (u' * mX)) * (mZ * (u' * mX)) = 1 ∧
    (mZ * u') * (mZ * u') = 1 ∧ ((mA * u') * (u' * mX)) ^ 3 = 1 ∧
    ((mA * u') * u') * ((mA * u') * u') = 1 ∧ ((u' * mX) * u') ^ 3 = 1 ∧ mA * u' ≠ mZ := by
  rcases mU' with rfl | rfl <;> decide +kernel

end CFSG.Quasithin
