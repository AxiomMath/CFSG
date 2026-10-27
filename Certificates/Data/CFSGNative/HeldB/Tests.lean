module

public import Certificates.Data.CFSGNative.PairSchreier.Core

public section

namespace CFSG.Sporadic.HeldB.Native

open CFSG.Sporadic.Schreier.PairNative

@[expose] def commB (t : Array Nat) (bs : List Nat) (w : List (Array Nat)) : Bool :=
  bs.all fun b => t[evR w b]! == evR w t[b]!

@[expose] def twistInvB (t : Array Nat) (bs : List Nat) (w : List (Array Nat)) : Bool :=
  bs.all fun b => t[evR w t[evR w b]!]! == b

end CFSG.Sporadic.HeldB.Native
