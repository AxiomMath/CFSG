module

public import Certificates.Data.ONanB2Tabs

public section

namespace CFSG.OddStandard.ONanRec.CM

@[expose] def aW : List Nat := [0]
@[expose] def bW : List Nat := [2]
@[expose] def cW : List Nat := [4]

@[expose] def s1W : List Nat := r1W ++ r2W ++ r2W
@[expose] def s2W : List Nat := r1W ++ r2W

@[expose] def x5W : List Nat := yW ++ bW ++ cW

@[expose] def g2W : List Nat := gW ++ fW ++ wpow yW 3

@[expose] def substG2 (c : Nat) : List Nat :=
  if c = 10 then g2W else if c = 11 then invWord g2W else [c]

@[expose] def badWords : List (List Nat) :=
  [[1, 1, 2, 4], [1, 2, 3, 4], [1, 2, 4], [1, 2, 4, 3], [1, 3, 4], [1, 4], [1, 4, 3], [2, 4]]

end CFSG.OddStandard.ONanRec.CM
