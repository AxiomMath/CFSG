module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

abbrev BM : Type := Fin 5 → ℕ

@[expose] def toMat (A : BM) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => if (A i).testBit j then 1 else 0

@[expose] def rowMul (a : ℕ) (B : BM) : ℕ :=
  (if a.testBit 0 then B 0 else 0) ^^^ (if a.testBit 1 then B 1 else 0) ^^^
    (if a.testBit 2 then B 2 else 0) ^^^ (if a.testBit 3 then B 3 else 0) ^^^
      (if a.testBit 4 then B 4 else 0)

@[expose] def bmul (A B : BM) : BM := fun i => rowMul (A i) B

@[expose] def bone : BM := ![1, 2, 4, 8, 16]

theorem ite_xor_zmod (p q : Bool) :
    (if (p ^^ q) = true then (1 : ZMod 2) else 0) =
      (if p = true then 1 else 0) + (if q = true then 1 else 0) := by
  cases p <;> cases q <;> decide

theorem ite_and_zmod (p q : Bool) :
    (if (p && q) = true then (1 : ZMod 2) else 0) =
      (if p = true then 1 else 0) * (if q = true then 1 else 0) := by
  cases p <;> cases q <;> decide

theorem testBit_ite (c : Bool) (n j : ℕ) :
    (if c = true then n else 0).testBit j = (c && n.testBit j) := by
  cases c <;> simp

theorem toMat_bmul (A B : BM) : toMat (bmul A B) = toMat A * toMat B := by
  ext i j
  simp only [toMat, bmul, rowMul, of_apply, mul_apply, Fin.sum_univ_five, Nat.testBit_xor,
    testBit_ite, ite_xor_zmod, ite_and_zmod]
  rfl

theorem toMat_bone : toMat bone = 1 := by decide

end CFSG.Quasithin.JonesParshall.Curtis
