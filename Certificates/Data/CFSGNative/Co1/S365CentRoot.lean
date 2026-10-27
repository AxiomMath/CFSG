module

public import Certificates.Data.CFSGNative.Co1.S365Coset
public import Certificates.Data.CFSGNative.Co1.S365U

public section

namespace CFSG.Sporadic.Co1.S365CentNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365Native
  CFSG.Sporadic.Co1.S365UNative

@[expose] def orthAllN (gs : List Nat) (u : Nat) : Bool := gs.all fun g => !parity24N (u &&& g)

@[expose] def hasPreN (B : List (Nat × Nat)) (Mt : Array Nat) (u : Nat) : Bool :=
  match memPre B u with
  | some q => onePlus Mt q == u
  | none => false

@[expose] def rootP (qr pts : Array Nat) (pos : Array UInt32) (n : Nat) (gs : List Nat)
    (x : Nat) : Bool :=
  orthAllN gs x && tyLabN qr pts pos n x == 3

@[expose] def rootCountNB (B : List (Nat × Nat)) (qr pts : Array Nat) (pos : Array UInt32)
    (n : Nat) (gs : List Nat) (Mt : Array Nat) (cnt : Nat) : Bool :=
  countBelow (rootP qr pts pos n gs) 16777216 0 == cnt &&
    countBelow (fun x => rootP qr pts pos n gs x && !hasPreN B Mt x) 16777216 0 == 0

@[expose] def rootCountN (qr pts : Array Nat) (pos : Array UInt32) (n : Nat) (gs : List Nat)
    (Mt : Array Nat) (cnt : Nat) : Bool :=
  rootCountNB (imBasis Mt) qr pts pos n gs Mt cnt

end CFSG.Sporadic.Co1.S365CentNative
