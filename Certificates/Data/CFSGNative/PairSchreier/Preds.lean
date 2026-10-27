module

public import Certificates.Data.CFSGNative.PairSchreier.Core

public section

namespace CFSG.Sporadic.Schreier.PairNative

@[expose] def ordPred (bs : List Nat) (m : Nat) (w : List (Array Nat)) : Bool := ordB bs w m

@[expose] def pairPred (bs : List Nat) (my : Nat) (x : List (Array Nat))
    (conds : List (List Bool × Nat)) (y : List (Array Nat)) : Bool :=
  ordB bs y my && condsOK bs x y conds

end CFSG.Sporadic.Schreier.PairNative
