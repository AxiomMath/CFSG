module

public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.InnerCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.Sporadic.HeldB.Native

@[expose] def heT1cArr : Array Nat :=
  compA 8330 (heGen 1) (compA 8330 heT1Arr (invCand 8330 (heGen 1)))

end CFSG.Sporadic.HeldB
