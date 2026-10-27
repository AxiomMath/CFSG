module

public import CFSG.YGroups.Y443.Native.Words

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native CFSG.Monster.SpinLattice CFSG.Monster.B CFSG.Monster.B.Rep4371
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible

theorem L_zero : L 0 = [Native.Gen.tau] := by rfl

theorem L_one : L 1 = [Native.Gen.rho (false, 1, 0)] := by rfl

theorem M_zero : M 0 = tauB := by
  rw [M, L_zero]
  show 1 * Native.Gen.tau.toLin = tauB
  rw [one_mul]
  rfl

theorem orderOf_M_zero : orderOf (M 0) = 3 := by
  rw [M_zero]
  exact orderOf_tauB

theorem M_zero_ne_one : M 0 ≠ 1 := by
  rw [M_zero]
  exact tauB_ne_one

theorem thetaN_one : Model.thetaN 1 = 0 := by decide

theorem toC_one : toC 1 = basisC 0 := by
  simpa using toC_two_pow (0 : Fin 12)

theorem pauliQ_one_zero : pauliQ (false, 1, 0) = XQ ⟨toC 1, 0⟩ := by
  rw [pauliQ, XQ_eq]
  congr 1
  refine SpinCoord.ext rfl ?_ ?_
  · rw [toSC_a, pauli_a]
  · rw [toSC_δ, pauli_d, thetaD_toC, thetaN_one]

theorem M_one : M 1 = rhoEquiv (XQ ⟨basisC 0, 0⟩) := by
  rw [M, L_one, ← toC_one]
  show 1 * (Native.Gen.rho (false, 1, 0)).toLin = _
  rw [one_mul, Native.Gen.toLin_rho, pauliQ_one_zero]

end CFSG.YGroups.Y443
