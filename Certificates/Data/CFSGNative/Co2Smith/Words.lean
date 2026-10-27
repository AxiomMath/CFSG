module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def wRows (L : Array (Array Nat)) : List Nat → Array Nat
  | [] => idRows 22
  | k :: w => mulRows 22 L[k]! (wRows L w)

@[expose] def colAct (R : Array Nat) (v : Nat) : Nat := vecMulN 22 (transposeRows 22 R) v

@[expose] def colActT (T : Array Nat) (v : Nat) : Nat := vecMulN 22 T v

@[expose] def fixesT (T : Array Nat) (v : Nat) : Bool := vecMulN 22 T v == v

end CFSG.Sporadic.Co2Smith.Native
