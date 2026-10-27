module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix

abbrev BM : Type := Fin 6 → ℕ

@[expose] def toMat (A : BM) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => if (A i).testBit j then 1 else 0

@[expose] def rowMul (a : ℕ) (B : BM) : ℕ :=
  (if a.testBit 0 then B 0 else 0) ^^^ (if a.testBit 1 then B 1 else 0) ^^^
    (if a.testBit 2 then B 2 else 0) ^^^ (if a.testBit 3 then B 3 else 0) ^^^
      (if a.testBit 4 then B 4 else 0) ^^^ (if a.testBit 5 then B 5 else 0)

@[expose] def bmul (A B : BM) : BM := fun i => rowMul (A i) B

@[expose] def bone : BM := ![1, 2, 4, 8, 16, 32]

@[expose] def btrans (A : BM) : BM := fun i =>
  (if (A 0).testBit i then 1 else 0) ^^^ (if (A 1).testBit i then 2 else 0) ^^^
    (if (A 2).testBit i then 4 else 0) ^^^ (if (A 3).testBit i then 8 else 0) ^^^
      (if (A 4).testBit i then 16 else 0) ^^^ (if (A 5).testBit i then 32 else 0)

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
  simp only [toMat, bmul, rowMul, of_apply, mul_apply, Fin.sum_univ_six, Nat.testBit_xor,
    testBit_ite, ite_xor_zmod, ite_and_zmod]
  rfl

theorem toMat_bone : toMat bone = 1 := by decide

theorem toMat_btrans (A : BM) : toMat (btrans A) = (toMat A)ᵀ := by
  ext i j
  simp only [toMat, btrans, of_apply, transpose_apply, Nat.testBit_xor, testBit_ite]
  fin_cases j <;> simp [Nat.testBit]

@[expose] def gramB : BM := ![32, 16, 8, 4, 2, 1]

@[expose] def xB : Fin 3 → BM :=
  ![![3, 2, 4, 8, 48, 32], ![1, 6, 4, 24, 16, 32], ![1, 2, 12, 8, 16, 32]]

@[expose] def yB : Fin 3 → BM :=
  ![![1, 3, 4, 8, 16, 48], ![1, 2, 6, 8, 24, 32], ![1, 2, 4, 12, 16, 32]]

@[expose] def sB : Fin 3 → BM :=
  ![![2, 1, 4, 8, 32, 16], ![1, 4, 2, 16, 8, 32], ![1, 2, 8, 4, 16, 32]]

theorem bit_symp : ∀ s,
    bmul (bmul (btrans (xB s)) gramB) (xB s) = gramB ∧
      bmul (bmul (btrans (yB s)) gramB) (yB s) = gramB ∧
        bmul (bmul (btrans (sB s)) gramB) (sB s) = gramB := by
  decide +kernel

theorem bit_invol : ∀ s,
    bmul (xB s) (xB s) = bone ∧ bmul (yB s) (yB s) = bone ∧ bmul (sB s) (sB s) = bone := by
  decide +kernel

theorem bit_rel : ∀ s,
    sB s = bmul (bmul (xB s) (yB s)) (xB s) ∧ sB s = bmul (bmul (yB s) (xB s)) (yB s) ∧
      bmul (xB s) (yB s) = bmul (yB s) (sB s) ∧ bmul (xB s) (yB s) = bmul (sB s) (xB s) ∧
        xB s = bmul (bmul (yB s) (sB s)) (yB s) ∧ yB s = bmul (bmul (xB s) (sB s)) (xB s) := by
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
