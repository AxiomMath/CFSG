module

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

@[expose] def noneDims : List Nat := [12, 13, 15, 16, 17, 18, 19, 21]

@[expose] def noneHints12 : List (Nat × Nat × Nat × Nat) := []

@[expose] def noneHints13 : List (Nat × Nat × Nat × Nat) := []

@[expose] def noneHints15 : List (Nat × Nat × Nat × Nat) :=
  [(0, 0, 3, 6), (0, 0, 91, 10), (0, 0, 107, 6), (0, 0, 115, 10), (0, 1, 5, 6), (0, 1, 51, 10),
   (0, 1, 61, 10), (0, 1, 71, 10), (0, 1, 83, 10), (0, 1, 93, 6), (0, 1, 101, 10), (1, 0, 5, 6),
   (1, 0, 51, 10), (1, 0, 61, 10), (1, 0, 71, 10), (1, 0, 85, 6), (1, 0, 99, 6), (1, 0, 109, 10),
   (1, 1, 3, 6), (1, 1, 5, 6), (1, 1, 51, 10), (1, 1, 53, 10), (1, 1, 63, 10), (1, 1, 83, 6),
   (1, 1, 85, 10), (1, 1, 99, 10), (1, 1, 101, 6), (1, 2, 9, 6), (1, 2, 51, 10), (1, 2, 61, 10),
   (1, 2, 75, 10), (1, 2, 83, 6), (1, 2, 93, 10), (1, 2, 105, 6), (2, 1, 9, 6), (2, 1, 51, 10),
   (2, 1, 61, 10), (2, 1, 75, 10), (2, 1, 89, 10), (2, 1, 99, 10), (2, 1, 109, 6), (2, 2, 5, 6),
   (2, 2, 93, 10), (2, 2, 109, 10), (2, 2, 117, 6)]

@[expose] def noneHints16 : List (Nat × Nat × Nat × Nat) := []

@[expose] def noneHints17 : List (Nat × Nat × Nat × Nat) := []

@[expose] def noneHints18 : List (Nat × Nat × Nat × Nat) :=
  [(1, 1, 16, 10), (1, 1, 32, 36)]

@[expose] def noneHints19 : List (Nat × Nat × Nat × Nat) :=
  [(1, 1, 95, 10), (1, 1, 111, 10)]

@[expose] def noneHints21 : List (Nat × Nat × Nat × Nat) :=
  [(0, 0, 27, 10), (0, 0, 39, 10), (0, 0, 43, 10), (0, 0, 51, 10), (0, 0, 67, 10),
   (0, 0, 103, 10), (0, 1, 47, 10), (0, 2, 19, 10), (0, 2, 35, 10), (0, 2, 63, 10),
   (0, 2, 67, 10), (0, 2, 115, 10), (1, 0, 31, 6), (1, 2, 47, 6), (2, 0, 19, 10), (2, 0, 35, 10),
   (2, 0, 63, 10), (2, 0, 67, 10), (2, 0, 115, 10), (2, 1, 31, 10), (2, 2, 29, 10),
   (2, 2, 39, 10), (2, 2, 45, 10), (2, 2, 53, 10), (2, 2, 69, 10), (2, 2, 103, 10)]

@[expose] def noneHints (d : Nat) : List (Nat × Nat × Nat × Nat) :=
  match d with
  | 12 => noneHints12
  | 13 => noneHints13
  | 15 => noneHints15
  | 16 => noneHints16
  | 17 => noneHints17
  | 18 => noneHints18
  | 19 => noneHints19
  | 21 => noneHints21
  | _ => []

end CFSG.LargeExtraspecial.SL4Mod.Native
