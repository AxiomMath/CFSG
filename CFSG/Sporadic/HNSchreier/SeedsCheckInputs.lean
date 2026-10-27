module

public import Certificates.Data.CFSGNative.He.Fp
public import Certificates.Data.CFSGNative.HN.Data
public meta import Certificates.Data.CFSGNative.He.Fp
public meta import Certificates.Data.CFSGNative.HN.Data

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native

@[expose] def rowsA : Array (Array Nat) := rowsOf 5 133 CFSG.Sporadic.HN.Native.seedA

@[expose] def rowsB : Array (Array Nat) := rowsOf 5 133 CFSG.Sporadic.HN.Native.seedB

@[expose] def notIdM (d : Nat) (X : Array (Array Nat)) : Bool :=
  !(Nat.all d fun i _ => Nat.all d fun j _ => X[i]![j]! % 5 == if i = j then 1 else 0)

@[expose] def wordM (Ms : Nat → Array (Array Nat)) (w : List Nat) : Array (Array Nat) :=
  w.foldl (fun P l => mulM 5 133 P (Ms l)) (idM 133)

@[expose] def seedSel (A B : Array (Array Nat)) (l : Nat) : Array (Array Nat) :=
  if l = 1 then A else if l = 2 then B else idM 133

@[expose] def gWord : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]

@[expose] def gInvWord : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1]

@[noinline, expose] def seedChecks (A B : Array (Array Nat)) : Bool :=
  let AB := mulM 5 133 A B
  let G := wordM (seedSel A B) gWord
  let Gi := wordM (seedSel A B) gInvWord
  let X := mulM 5 133 (mulM 5 133 (mulM 5 133 A Gi) B) G
  powM 5 133 A 2 == idM 133 && notIdM 133 A && powM 5 133 B 3 == idM 133 && notIdM 133 B &&
    powM 5 133 AB 22 == idM 133 && notIdM 133 (powM 5 133 AB 11) &&
    notIdM 133 (powM 5 133 AB 2) && mulM 5 133 G Gi == idM 133 &&
    powM 5 133 X 19 == idM 133 && notIdM 133 X

end CFSG.Sporadic.HNSchreier.Native
