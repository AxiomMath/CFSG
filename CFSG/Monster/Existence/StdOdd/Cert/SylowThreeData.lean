module

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

abbrev Letter : Type := Nat × Bool × Bool

@[expose] def gamTable : List Nat := [
  5, 1, 4, 3, 2, 0, 16, 15, 8, 9, 14, 13, 12, 11, 10, 7, 6, 26,
  25, 19, 21, 20, 24, 23, 22, 18, 17, 36, 33, 35, 31, 30, 32, 28, 34, 29,
  27, 42, 45, 44, 40, 41, 37, 43, 39, 38, 51, 47, 52, 49, 50, 46, 48, 57,
  54, 58, 56, 53, 55, 63, 60, 62, 61, 59, 65, 64, 66, 67, 68, 69, 70, 71]

@[expose] def gWord : List Letter := [
  (8, false, true), (1, true, false), (50, false, true), (43, true, false),
  (60, false, true), (56, true, false), (67, false, true), (66, true, false)]

@[expose] def nWord (j : Nat) : List Letter :=
  [(j, true, false), (6 + 2 * j, true, false), (j, true, false)]

@[expose] def hWord (j : Nat) : List Letter :=
  [(j, false, true), (6 + 2 * j, true, true), (j, false, true)] ++ nWord j

@[expose] def rWord (i : Nat) : List Letter := gWord ++ nWord i ++ gWord.reverse

@[expose] def eWord (j : Nat) : List Letter := gWord ++ hWord j ++ gWord.reverse

@[expose] def torusExps : List (List Nat) := [
  [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0,
   2, 0, 1, 2, 0, 0, 0, 2, 1, 1, 1, 0, 2, 0, 1, 2, 0, 2, 2, 1, 1, 1, 0, 2, 2, 1,
   2, 2, 1, 1, 1, 1, 2, 2, 2, 0, 1, 1, 2, 0, 2, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 2, 1, 2, 0, 0, 0, 0, 2, 2,
   1, 1, 1, 2, 1, 2, 0, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 0, 1, 1,
   2, 1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 2],
  [0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 1, 1, 0, 2, 1, 1, 1, 2, 0, 0, 0, 2, 0, 1,
   1, 2, 2, 1, 1, 2, 0, 0, 0, 0, 2, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 2, 1, 0, 1, 2,
   0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 2, 0, 0, 2, 1, 1, 2, 0, 2, 1, 1, 2, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 2,
   0, 0, 2, 0, 2, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 2, 0,
   1, 0, 1, 2, 2, 1, 1, 2, 1, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 1, 2, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2, 0, 2, 1, 1, 1, 1, 1, 0, 2, 1,
   2, 1, 1, 1, 2, 0, 2, 1, 2, 1, 1, 2, 1, 0, 2, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0,
   2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 0, 0, 0, 0]]

@[expose] def tAidx : List Nat := [1, 3]

@[expose] def tBidx : List Nat := [2, 3, 4, 5, 0, 2, 3, 4]

end CFSG.Monster.Existence.StdOdd.Cert
