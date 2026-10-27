module

public import CFSG.Sporadic.SuzOddCore.Arrays
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.SuzOddCore.Arrays
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native

@[expose] def permOK (n : Nat) (t : Array Nat) : Bool := t.size == n && isInvA n t (invCand n t)

@[expose] def derivsOK (k : Nat) (W : Array (List Int)) : Bool :=
  allLt W.size fun j => decide (j < k) || lettersOK j W[j]!

end CFSG.Sporadic.SuzOddCore
