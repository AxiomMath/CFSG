module

public import CFSG.Sporadic.Schreier.ONActionData
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def qonStrongArrs : Array (Array Nat) :=
  strongArrs nPts (natTab (vorbit (digitsW Data.rootDigits)).alpha)
    (natTab (vorbit (digitsW Data.rootDigits)).beta) Data.strongWords

end CFSG.ONSchreier
