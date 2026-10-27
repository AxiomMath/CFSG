
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
public import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheckBase

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer

@[expose] def fi22ExtDArr : Array Nat := fi22ExtSmallPointsNat.toArray

@[expose] def fi22ExtPosArr : Array Nat := Id.run do
  let mut p : Array Nat := Array.replicate 3510 256
  for i in [0:256] do
    p := p.set! fi22ExtDArr[i]! i
  return p

@[expose] def fi22ExtQiArr : Array Nat := invCand 3510 (fi22ExtArr 0)

@[expose] def fi22ExtViArr : Array Nat := invCand 3510 (fi22ExtArr 1)

@[expose] def fi22InP (g : Array Nat) : Bool :=
  siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 g

@[expose] def fi22InT (g : Array Nat) : Bool :=
  siftA 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] 0 g

end CFSG.Sporadic.FischerOddCore
