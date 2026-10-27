module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Matrix

@[expose] def fusionA : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 1, 1, 1, 0; 0, 0, 1, 0; 1, 0, 0, 1]

@[expose] def fusionB : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 1, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1]

@[expose] def fusionF : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

@[expose] def fusionR : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 1, 1; 1, 0, 1, 0; 0, 0, 1, 1]

@[expose] def fusionZ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 1, 0; 1, 0, 1, 0; 0, 0, 1, 0; 1, 1, 0, 1]

@[expose] def fusionY : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 0; 1, 1, 1, 1]

@[expose] def fusionWord (Q : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fusionB * fusionF * Q * fusionF ^ 2 * Q * fusionF * Q * fusionF ^ 2 * Q * fusionF * Q

@[expose] def fusionPplus : Finset (Fin 4 → ZMod 2) :=
  {![1, 0, 0, 0], ![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 0, 1], ![0, 1, 1, 1]}

theorem fusionA_mul_self : fusionA * fusionA = 1 := by decide

theorem fusionB_mul_self : fusionB * fusionB = 1 := by decide

theorem fusionF_mul_sq : fusionF * fusionF ^ 2 = 1 := by decide

theorem fusionF_sq_mul : fusionF ^ 2 * fusionF = 1 := by decide

theorem fusionZ_mul_self : fusionZ * fusionZ = 1 := by decide

theorem fusionY_mul_pow_three : fusionY * fusionY ^ 3 = 1 := by decide

theorem fusionY_pow_three_mul : fusionY ^ 3 * fusionY = 1 := by decide

@[expose] def fusionUnitA : GL (Fin 4) (ZMod 2) :=
  ⟨fusionA, fusionA, fusionA_mul_self, fusionA_mul_self⟩

@[expose] def fusionUnitB : GL (Fin 4) (ZMod 2) :=
  ⟨fusionB, fusionB, fusionB_mul_self, fusionB_mul_self⟩

@[expose] def fusionUnitF : GL (Fin 4) (ZMod 2) :=
  ⟨fusionF, fusionF ^ 2, fusionF_mul_sq, fusionF_sq_mul⟩

@[expose] def fusionUnitZ : GL (Fin 4) (ZMod 2) :=
  ⟨fusionZ, fusionZ, fusionZ_mul_self, fusionZ_mul_self⟩

@[expose] def fusionUnitY : GL (Fin 4) (ZMod 2) :=
  ⟨fusionY, fusionY ^ 3, fusionY_mul_pow_three, fusionY_pow_three_mul⟩

@[simp] theorem val_fusionUnitA : (fusionUnitA : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionA := rfl

@[simp] theorem val_fusionUnitB : (fusionUnitB : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionB := rfl

@[simp] theorem val_fusionUnitF : (fusionUnitF : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionF := rfl

@[simp] theorem val_fusionUnitZ : (fusionUnitZ : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionZ := rfl

@[simp] theorem val_fusionUnitY : (fusionUnitY : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionY := rfl

end CFSG.OddTranspositions.PartThree.Wong
