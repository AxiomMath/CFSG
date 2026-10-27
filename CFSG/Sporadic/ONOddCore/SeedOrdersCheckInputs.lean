module

public import CFSG.Sporadic.Schreier.ONActionData
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def ppow (x : Array Nat) : Nat → Array Nat
  | 0 => pid nPts
  | k + 1 => pcomp nPts x (ppow x k)

end CFSG.Sporadic.ONOddCore
