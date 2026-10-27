module

public import Certificates.Data.G23K7b

public section

namespace Certificates.G2Gen

open Certificates.G2ThreeMax
open CFSG.CGT.PushingUpLit.CGT6.EmbModule (nzFlat)

@[expose] def dW : List ℕ := [0, 5, 0, 0, 5, 0]

@[expose] def gW : List ℕ := [3, 0, 2, 6, 5, 7]

@[expose] def giW : List ℕ := [6, 4, 7, 3, 1, 2]

@[expose] def yInW : List ℕ := giW ++ dW ++ gW ++ dW

@[expose] def g1W : List ℕ := [7]

@[expose] def g1iW : List ℕ := [6]

@[expose] def g2W : List ℕ := [3]

@[expose] def g2iW : List ℕ := [2]

@[expose] def c1W : List ℕ := [6, 5]

@[expose] def c1iW : List ℕ := [4, 7]

@[expose] def c2W : List ℕ := [2, 1]

@[expose] def yOutW : List ℕ := c1W ++ c1W ++ c2W ++ c1W ++ c2W ++ c1iW ++ c2W

@[expose] def mpowArr (a : Array ℕ) : ℕ → Array ℕ
  | 0 => idArr
  | n + 1 => mmul a (mpowArr a n)

@[expose] def g2GenCheck : Bool :=
  let d := wordArr dW
  let yi := wordArr yInW
  let yo := wordArr yOutW
  (mmul d d == idArr) && (d[45]! % 3 == 2) &&
  (mmul (wordArr gW) (wordArr giW) == idArr) &&
  (mpowArr yi 13 == idArr) && nzFlat yi 2 &&
  (mmul (wordArr g1W) (wordArr g1iW) == idArr) &&
  (mmul (wordArr g2W) (wordArr g2iW) == idArr) &&
  (mmul (wordArr c1W) (wordArr c1iW) == idArr) &&
  (mpowArr yo 13 == idArr) && nzFlat yo 2

end Certificates.G2Gen
