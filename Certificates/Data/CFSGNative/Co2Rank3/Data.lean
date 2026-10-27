module

public section

namespace CFSG.Sporadic.Co2Rank3.Native

@[expose] def refineBase : List Nat := [0, 3, 1, 2, 522, 360]

@[expose] def refineBounds : List Nat := [2300, 891, 896, 192, 10, 12]

@[expose] def level1Idx : List Nat := [0, 2, 3, 4, 5, 6, 7, 8, 9, 10]

@[expose] def level2Idx : List Nat := [3, 4, 5, 6, 7, 8, 9, 10]

@[expose] def stabWords (_ : Unit := ()) : List (List Int) :=
  [[-4, 8, 5, -6, -6, -4, -6], [-4, 11, 3, 9, 6, 3, -8], [-6, 9, 8, -5]]

@[expose] def p0Roots : List (Nat × Nat) := [(0, 1), (1, 1408), (3, 891)]

@[expose] def stabRoots : List (Nat × Nat) :=
  [(0, 1), (1, 896), (2, 512), (3, 1), (4, 336), (5, 512), (36, 42)]

@[expose] def p01Roots : List (Nat × Nat) :=
  [(0, 1), (1, 1), (2, 567), (3, 567), (4, 324), (8, 840)]

end CFSG.Sporadic.Co2Rank3.Native
