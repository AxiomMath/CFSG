module

public import CFSG.Monster.B.Fischer.Fi22Outer
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Monster.B.Fischer.Fi22Outer
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.RankThree.Native.Fi22U

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def commA (n : Nat) (a b : Array Nat) : Array Nat :=
  compA n (compA n (compA n b a) (invCand n b)) (invCand n a)

end CFSG.RankThree.Native.Fi22U
