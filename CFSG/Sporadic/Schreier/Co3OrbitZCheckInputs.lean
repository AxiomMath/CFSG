module

public import CFSG.Sporadic.Schreier.Co3Cert
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3OrigArrs : Array (Array Nat) := co3ChainArrs.extract 0 2

@[expose] def co3OrbitZ : Array (List Nat) × Array Nat × Array Nat :=
  hashSearch co3OrigArrs co3IzNat 170775

end CFSG.Sporadic.Schreier.Co3
