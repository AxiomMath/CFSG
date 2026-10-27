module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Sporadic.Recognition.HSPinned

@[expose] def isoList : List ℕ := [
  0, 64, 41, 77, 4, 7, 21, 23, 73, 97,
  1, 46, 93, 80, 53, 12, 50, 51, 49, 24,
  32, 57, 14, 15, 43, 88, 89, 47, 60, 54,
  13, 37, 81, 66, 62, 65, 75, 36, 28, 92,
  98, 27, 22, 87, 2, 35, 95, 6, 56, 3,
  10, 29, 90, 5, 8, 25, 31, 82, 69, 61,
  84, 38, 70, 58, 44, 16, 63, 67, 79, 11,
  48, 83, 18, 86, 55, 17, 71, 96, 94, 52,
  76, 9, 72, 34, 40, 99, 68, 26, 19, 39,
  59, 20, 30, 78, 33, 91, 74, 42, 85, 45]

@[expose] def isoFun (i : Fin 100) : Fin 100 :=
  ⟨(isoList.getD i 0) % 100, Nat.mod_lt _ (by norm_num)⟩

end CFSG.Sporadic.Recognition.HSPinned
