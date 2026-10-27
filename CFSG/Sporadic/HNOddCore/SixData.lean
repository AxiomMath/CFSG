module

public import Init

public section

namespace CFSG.Sporadic.HNOddCore.SixData

@[expose] def wa : List Int := [-6, -3, 7]

@[expose] def ea : Nat := 3

@[expose] def wb : List Int := [-6, 10, -7, -12]

@[expose] def eb : Nat := 4

@[expose] def dWords : Array (List Int) :=
  #[[], [], [-2, 1, 2], [2, -1, 3, 1, -2], [-1, -4, -1, 3, 1, 4, 1], [-2, -2, -3, 5, 2, 2], [-5, -4,
    6, 4, 5], [-3, -7, -3, -6, -4, 3, 4, 6], [-3, -7, -8, -4, -8, -3, -6, -8, -2, -8, 1, 6, 2]]

@[expose] def dBase : List (Fin 1100) := [0, 2, 1, 6]

@[expose] def dSizes : List Nat := [1100, 336, 30, 4]

end CFSG.Sporadic.HNOddCore.SixData
