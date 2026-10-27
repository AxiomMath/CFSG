module

public import CFSG.Sporadic.Schreier.ONActionData
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public import Certificates.Data.CFSGNative.Schreier.Merge
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.ON.Native

@[expose] def lineTabs : VOrbit :=
  lineBFS colsA colsB (digitsW CFSG.ONSchreier.Data.rootDigits) 122760

@[expose] def dArr0 : Array Nat := natTab lineTabs.alpha

@[expose] def dArr1 : Array Nat := natTab lineTabs.beta

@[expose] def primReps : List Nat := [0, 1, 2, 4, 9]

@[expose] def primSizes : List Nat := [1, 6384, 52136, 58653, 5586]

end CFSG.Sporadic.ONOddCore
