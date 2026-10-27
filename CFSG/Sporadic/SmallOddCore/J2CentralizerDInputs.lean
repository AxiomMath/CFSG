module

public import CFSG.Sporadic.SmallOddCore.J2LocalCheck
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public meta import CFSG.Sporadic.SmallOddCore.J2LocalCheck
public meta import CFSG.Sporadic.Schreier.PairJ2Check
public import Certificates.Certificate2233
public import Certificates.Certificate2234
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Certificates
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def commW (n : Nat) (gs : List (Array Nat)) (w : List (Array Nat)) : Bool :=
  gs.all fun g => allLt n fun i => evR w g[i]! == g[evR w i]!

end CFSG.Sporadic.SmallOddCore
