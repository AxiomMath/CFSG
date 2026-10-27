module

public section

namespace CFSG.D4Hex

@[expose] def f48NWord : List Nat := [3]

@[expose] def f48FWords : List (List Nat) := [[6], [7, 3, 5, 6, 0, 6, 1, 3, 7, 0]]

@[expose] def f48Base : Nat := 71

@[expose] def f48QWord : List Nat := [4, 7, 3, 7, 3, 7, 1, 5, 7, 4, 7, 4]

@[expose] def f48BWords : List (List Nat) :=
  [[], [2], [7, 3, 2, 4, 7], [0], [1], [7, 5, 1, 4, 7], [7, 3, 4, 0, 5, 7], [0, 7, 4, 2, 3, 7]]

@[expose] def f48Order : Nat := 211341312

@[expose] def f48Order3 : Nat := 634023936

end CFSG.D4Hex
