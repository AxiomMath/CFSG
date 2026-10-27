module

public import Certificates.Data.Kernel.SporSch.LySeven
public import Certificates.Data.CFSGNative.Ly.Orbit

public section

namespace CFSG.KS.SporSch.LyK

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Ly.Native

@[expose] noncomputable def keyOfD (D : Nat) : ByteArray :=
  encodeDigits fun p => if p < 826 then fld(D, 4 * p, 15) else 0

@[expose] noncomputable def upOfD (w S D : Nat) : Nat :=
  foldN (nat_lit 777) (fun p acc => Nat.lor acc
    (Nat.shiftLeft fld(D, Nat.mul (nat_lit 4) p, nat_lit 15)
      (Nat.add (Nat.mul S (Nat.mod p (nat_lit 111))) (Nat.mul w (Nat.div p (nat_lit 111))))))
    (nat_lit 0)

@[expose] noncomputable def digWalk (D : Nat) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun ch _ ih i => bAnd(Nat.beq (Nat.sub (Char.toNat ch) (nat_lit 48))
      fld(D, Nat.mul (nat_lit 4) i, nat_lit 15), ih (Nat.succ i))) cs

@[expose] noncomputable def lane7 (w S : Nat) (R : Array Nat) : Nat :=
  foldN (nat_lit 49) (fun t acc => Nat.lor acc (Nat.shiftLeft (R[t]!)
    (Nat.add (Nat.mul S (Nat.div t (nat_lit 7))) (Nat.mul w (Nat.mod t (nat_lit 7)))))) (nat_lit 0)

end CFSG.KS.SporSch.LyK

end
