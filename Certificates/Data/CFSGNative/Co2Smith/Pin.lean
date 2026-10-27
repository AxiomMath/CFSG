module

public import Certificates.Data.CFSGNative.Co2Smith.Check

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def frameNeOK (seeds : Array (Array Nat)) : Bool := (fRows seeds)[0]! != idRows 22

@[expose] def stdRows (_ : Unit := ()) : Array (Array Nat) := #[
  #[2, 3, 8, 12, 32, 48, 128, 192], #[3, 2, 12, 8, 48, 32, 192, 128],
  #[4, 8, 5, 10, 64, 128, 80, 160], #[5, 10, 4, 8, 80, 160, 64, 128],
  #[16, 32, 64, 128, 17, 34, 68, 136], #[17, 34, 68, 136, 16, 32, 64, 128],
  #[1, 4, 2, 8, 16, 64, 32, 128], #[1, 2, 16, 32, 4, 8, 64, 128]]

@[expose] def colAct8 (R : Array Nat) (v : Nat) : Nat := vecMulN 8 (transposeRows 8 R) v

@[expose] def xRows (c : Nat) : Array Nat :=
  Array.ofFn (n := 8) fun i =>
    ofBits 8 fun j => j % 2 == i.val % 2 && c.testBit (4 * (j / 2) + i.val / 2)

@[expose] def wRows8 : List Nat → Array Nat
  | [] => idRows 8
  | k :: w => mulRows 8 stdRows[k]! (wRows8 w)

@[expose] def fixesAll8 (M : Array Nat) : Bool :=
  (List.range 8).all fun a => colAct8 M (1 <<< a) == 1 <<< a

@[expose] def pinOK (c : Nat) : Bool :=
  pinRels.all fun r => fixesAll8 (powRows 8 (mulRows 8 (xRows c) (wRows8 r.1)) r.2)

@[expose] def pinUniqueOK (_ : Unit := ()) : Bool := (List.range 65536).all fun c => !pinOK c || c == 24505

end CFSG.Sporadic.Co2Smith.Native
