module

public import CFSG.Sporadic.Schreier.Co3Cert
public import CFSG.Sporadic.Schreier.Co3FaithfulData
public import Certificates.Data.CFSGNative.Co3.Data
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import CFSG.Sporadic.Schreier.Co3FaithfulData
public meta import Certificates.Data.CFSGNative.Co3.Data
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.SmallF2.Native

@[expose] def co3DiffRows : Array Nat :=
  (co3DiffIdx.map fun r => diagVec (co3FormWord r) ^^^ diagVec (co3FormWord 0)).toArray

end CFSG.Sporadic.Schreier.Co3
