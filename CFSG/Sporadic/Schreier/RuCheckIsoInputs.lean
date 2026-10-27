module

public import CFSG.Sporadic.Schreier.RuArrays
public import Certificates.Data.CFSGNative.Ru.Data
public meta import CFSG.Sporadic.Schreier.RuArrays
public meta import Certificates.Data.CFSGNative.Ru.Data
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native

@[expose] def ruSigmaA : Array ℕ :=
  Array.ofFn (n := 4060) fun i => ruHexAt ruBytesSigma (3 * i.val) 3

end CFSG.Sporadic.RuSchreier
