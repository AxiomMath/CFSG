module

public import Certificates.Data.CFSGNative.Co1.S365Coset

public section

namespace CFSG.Sporadic.Co1.S365CentNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365Native

@[expose] def applyPath (Mts : Array (Array Nat)) (path : List Nat) (v : Nat) : Nat :=
  path.foldl (fun acc l => vecMulN 24 Mts[l]! acc) v

@[expose] def pat4 (qr pts : Array Nat) (pos : Array UInt32) (n x y v : Nat) : Bool :=
  tyLabN qr pts pos n v == 1 && tyLabN qr pts pos n (v ^^^ x) == 1 &&
    tyLabN qr pts pos n (v ^^^ y) == 1 && tyLabN qr pts pos n (v ^^^ x ^^^ y) == 1

end CFSG.Sporadic.Co1.S365CentNative
