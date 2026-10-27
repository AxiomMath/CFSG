module

public import CFSG.Sporadic.J4.QT2LocNative
public import CFSG.Sporadic.J4.QTRankInvNative

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def decodeWord (s : String) : List Int :=
  s.toList.map fun c =>
    if 'a' ≤ c then ((c.toNat - 96 : Nat) : Int) else -((c.toNat - 64 : Nat) : Int)

@[expose] def kR (ℓ : Nat) : Array V2 := pathRows (repPaths.getD ℓ [])

@[expose] def uR (ℓ : Nat) : Array V2 := invRows (kR ℓ)

@[expose] def rV (ℓ : Nat) : V2 := pathVec (repPaths.getD ℓ [])

@[expose] def uBasis : Array (Array V2) := uTab (locMats ()) (locInvs ())

@[expose] def conjBy (L U R : Array V2) : Array V2 := mulRows (mulRows L U) R

end CFSG.Quasithin.J4Ov
