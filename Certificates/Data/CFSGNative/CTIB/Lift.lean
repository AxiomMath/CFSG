module

public import Certificates.Data.CFSGNative.CTIB.Arith
public import Certificates.Data.CFSGNative.CTIB.Data
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck

public section

namespace CFSG.Monster.B.CTIB.Native

open CFSG.Monster.B.Bin CFSG.Monster.B.Max2.Native

set_option compiler.extract_closed false

@[expose] def gArr (_ : Unit := ()) : Array Nat := gramRows.toArray

@[expose] def genImgs (l : Nat) : Array Nat :=
  ((List.range 22).map fun i =>
    signedImg (if l = 0 then quotRows1 else quotRows2) (if l = 0 then 3711077 else 3015616)
      i).toArray

@[expose] def minusIdRows (rows : List Nat) : Mat :=
  ((List.range 22).map fun i => #[rows.getD i 0 ^^^ 2 ^ i]).toArray

@[expose] def liftCheck (w : List Nat) (imgs rows : List Nat) (r : Nat) : Bool :=
  (autWord gArr genImgs w).toList == imgs && imgs.map (· % 2 ^ 22) == rows &&
    rows.length == 22 && rows.all (· < 2 ^ 22) &&
    eq22 (mul22 rows.toArray rows.toArray) id22 && rankOK 22 (minusIdRows rows) r

@[expose] def liftOK (_ : Unit) : Bool :=
  liftCheck liftWord6 liftImgs6 liftRows6 6 && liftCheck liftWord8 liftImgs8 liftRows8 8 &&
    liftCheck liftWord10 liftImgs10 liftRows10 10

end CFSG.Monster.B.CTIB.Native
