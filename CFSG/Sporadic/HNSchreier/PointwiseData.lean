module


public section

namespace CFSG.Sporadic.HNSchreier.PointwiseData

@[expose] def g0 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2]

@[expose] def hw : List Int := [12, 17, 3]

@[expose] def k1 : List Int := [-6, 9, -15, -2, 6, 16, 17, 17, -2, 1, 7, -1, 9, -11]

@[expose] def k2 : List Int :=
  [13, -14, -2, -16, -5, -1, 1, -9, 2, 9, -2, -16, 6, -13, 1, 13, 8, 13, -9, -11]

@[expose] def c1 : List Int := [1, 2, -8, 4, 3, 5, 9, 3, 13, 12, 11, -12, 13, 10, 17, 12, -14]

@[expose] def natP : List Nat := [4, 6, 9, 1, 11, 10, 2, 7, 8, 0, 5, 3]

@[expose] def natQ : List Nat := [10, 3, 6, 9, 7, 8, 2, 0, 1, 4, 11, 5]

@[expose] def natP2 : List Nat := [5, 8, 10, 4, 11, 7, 9, 6, 2, 3, 1, 0]

@[expose] def ufix : List Bool := [true, false, true, true, true]

@[expose] def tw : List (List Bool) :=
  [[], [true, true, true, true], [true, true, true, true, true, true], [true, true, true],
  [true], [true, false], [true, true, true, true, true], [false, true], [false, true, false],
  [false, true, true, true], [false], [true, true]]

end CFSG.Sporadic.HNSchreier.PointwiseData
