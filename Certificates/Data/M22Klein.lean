module

public import CFSG.Sporadic.Schreier.Enumeration
public meta import CFSG.Sporadic.Schreier.Enumeration
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426M22

open CFSG.Sporadic.Schreier

abbrev kA : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

abbrev kB : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

@[expose] def m22S : List (Equiv.Perm (Fin 22)) := [kA, kB]

@[expose] def xW : List Int :=
  [-1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, -2, -1,
  -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, -2, -1, 2, -1, -2, -2]

@[expose] def yW : List Int :=
  [2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, -1, 2, -1, -2, -1, 2, 1,
  2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2]

@[expose] def t1W : List Int :=
  [-2, -1, 2, 1, 2, 1, 2, -1, -2, -2, -1, 2, -1, -1, 2, -1, -2, -2, -1, -2, -1, -2, -1, 2, -1,
  -2, -1, -2, -1, 2]

@[expose] def t2W : List Int :=
  [-1, -2, -1, -1, -2, -1, -2, -2, -1, 2, -1, -1, 2, -1, -2, -1, -2, -1, -2, -2]

@[expose] def m22KleinOK (_ : Unit := ()) : Bool :=
  let x := evalCodes m22S xW
  let y := evalCodes m22S yW
  let t1 := evalCodes m22S t1W
  let t2 := evalCodes m22S t2W
  decide (x ^ 3 = 1) && decide (x ≠ 1) && decide (y ^ 3 = 1) && decide (y ≠ 1) &&
    decide (y ≠ x) && decide (y ≠ x ^ 2) && decide (x * y = y * x) && decide (t1 ^ 2 = 1) &&
    decide (t2 ^ 2 = 1) && decide (t1 ≠ 1) && decide (t2 ≠ 1) && decide (t1 ≠ t2) &&
    decide (t1 * t2 = t2 * t1) && decide (x * t1 = t1 * x) && decide (x * t2 = t2 * x) &&
    decide (y * t1 * y⁻¹ = t2) && decide (y * t2 * y⁻¹ = t1 * t2)

end CFSG.LocalAnalysis.GLTheoremA.KD1426M22
