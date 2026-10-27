module

public import CFSG.Sporadic.Schreier.Co3Data
public import Certificates.Data.CFSGNative.Co3Schreier.Forms

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3Bytes276 : ByteArray := co3Perm276Text.toUTF8

@[expose] def co3Bytes36 : ByteArray := co3Perm36Text.toUTF8

@[expose] def co3Bytes12 : ByteArray := co3Perm12Text.toUTF8

@[expose] def co3FormsBytes : ByteArray := co3FormsText.toUTF8

@[expose] def co3Arr276 (L : Nat) : Array Nat := hexLine co3Bytes276 3 276 L

@[expose] def co3Arr36 (L : Nat) : Array Nat := hexLine co3Bytes36 2 36 L

@[expose] def co3Arr12 (L : Nat) : Array Nat := hexLine co3Bytes12 1 12 L

@[expose] def co3Field276 (f : Nat) : Array (Array Nat) :=
  Array.ofFn (n := (co3Lines276.getD f (0, 0)).2) fun j =>
    co3Arr276 ((co3Lines276.getD f (0, 0)).1 + j.val)

@[expose] def co3Field36 (f : Nat) : Array (Array Nat) :=
  Array.ofFn (n := (co3Lines36.getD f (0, 0)).2) fun j =>
    co3Arr36 ((co3Lines36.getD f (0, 0)).1 + j.val)

@[expose] def co3Field12 (f : Nat) : Array (Array Nat) :=
  Array.ofFn (n := (co3Lines12.getD f (0, 0)).2) fun j =>
    co3Arr12 ((co3Lines12.getD f (0, 0)).1 + j.val)

@[expose] def co3FormWord (r : Nat) : Nat := formAt co3FormsBytes r

@[expose] def co3ChainArrs : Array (Array Nat) := co3Field276 0

@[expose] def co3CoprimeArrs : Array (Array Nat) := co3Field276 1

@[expose] def co3ZArr : Array Nat := (co3Field276 2)[0]!

@[expose] def co3TtArr : Array Nat := (co3Field276 3)[0]!

@[expose] def co3D0Arrs : Array (Array Nat) := co3Field276 4

@[expose] def co3TArrs : Array (Array Nat) := co3Field276 5

@[expose] def co3MArrs : Array (Array Nat) := co3Field276 6

@[expose] def co3M1Arrs : Array (Array Nat) := co3Field276 7

@[expose] def co3MCommArrs : Array (Array Nat) := co3Field276 8

@[expose] def co3M1CommArrs : Array (Array Nat) := co3Field276 9

@[expose] def co3JointArrs : Array (Array Nat) := co3Field276 10

@[expose] def co3Sp36Arrs : Array (Array Nat) := co3Field36 0

@[expose] def co3M36Arrs : Array (Array Nat) := co3Field36 1

@[expose] def co3CspArr : Array Nat := (co3Field36 2)[0]!

@[expose] def co3M112Arrs : Array (Array Nat) := co3Field12 0

@[expose] def co3C12Arr : Array Nat := (co3Field12 1)[0]!

end CFSG.Sporadic.Schreier.Co3
