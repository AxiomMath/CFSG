module

public import Certificates.Data.Kernel.TwistDce3.FoldQ

public section

namespace CFSG.KC.TwDce3Q

open CFSG.KC.TwDce (wLen wStr fld)
open CFSG.KC.YModel (fieldAt)

@[expose] noncomputable def ev4Q (PB : Nat) (F : Nat → Nat) (q s x y z v : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) (fun s x y z v => k s x y z v)
    (fun _ ih s x y z v =>
      TwDce.sB (Nat.land s (nat_lit 15)) fun a =>
      TwDce.sB (Nat.land (Nat.shiftRight s (nat_lit 4)) (nat_lit 15)) fun b =>
      TwDce.sB (Nat.land (Nat.shiftRight s (nat_lit 8)) (nat_lit 15)) fun c =>
      TwDce.sB (Nat.land (Nat.shiftRight s (nat_lit 12)) (nat_lit 15)) fun d =>
      TwDce.sB (fieldAt PB (F d) (fieldAt PB (F c) (fieldAt PB (F b) (fieldAt PB (F a) x)))) fun x' =>
      TwDce.sB (fieldAt PB (F d) (fieldAt PB (F c) (fieldAt PB (F b) (fieldAt PB (F a) y)))) fun y' =>
      TwDce.sB (fieldAt PB (F d) (fieldAt PB (F c) (fieldAt PB (F b) (fieldAt PB (F a) z)))) fun z' =>
      TwDce.sB (fieldAt PB (F d) (fieldAt PB (F c) (fieldAt PB (F b) (fieldAt PB (F a) v)))) fun v' =>
      TwDce.sB (Nat.shiftRight s (nat_lit 16)) fun s' => ih s' x' y' z' v')
    q s x y z v

@[expose] noncomputable def ev4T (PB : Nat) (F : Nat → Nat) (n s x y z v : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) (fun _ x y z v => k x y z v)
    (fun _ ih s x y z v =>
      TwDce.sB (Nat.land s (nat_lit 15)) fun a =>
      TwDce.sB (fieldAt PB (F a) x) fun x' =>
      TwDce.sB (fieldAt PB (F a) y) fun y' =>
      TwDce.sB (fieldAt PB (F a) z) fun z' =>
      TwDce.sB (fieldAt PB (F a) v) fun v' =>
      TwDce.sB (Nat.shiftRight s (nat_lit 4)) fun s' => ih s' x' y' z' v')
    n s x y z v

@[expose] noncomputable def isOneQ4 (PB : Nat) (F : Nat → Nat) (BS w : Nat) : Bool :=
  TwDce.sB w fun w =>
  TwDce.sB (fld BS (nat_lit 0) (nat_lit 65535)) fun b0 =>
  TwDce.sB (fld BS (nat_lit 16) (nat_lit 65535)) fun b1 =>
  TwDce.sB (fld BS (nat_lit 32) (nat_lit 65535)) fun b2 =>
  TwDce.sB (fld BS (nat_lit 48) (nat_lit 65535)) fun b3 =>
  ev4Q PB F (Nat.shiftRight (wLen w) (nat_lit 2)) (wStr w) b0 b1 b2 b3 fun s x y z v =>
  ev4T PB F (Nat.land (wLen w) (nat_lit 3)) s x y z v fun x y z v =>
    andB (Nat.beq x b0) (andB (Nat.beq y b1) (andB (Nat.beq z b2) (Nat.beq v b3)))

end CFSG.KC.TwDce3Q

end
