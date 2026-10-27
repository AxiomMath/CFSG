module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.J3C

open CFSG.KC.Enum

@[expose] noncomputable def e16 (F : Nat → Nat) (i : Nat) : Nat :=
  fld(F (Nat.shiftRight i (nat_lit 5)), Nat.mul (nat_lit 16) (Nat.land i (nat_lit 31)),
    nat_lit 65535)

@[expose] noncomputable def e64 (F : Nat → Nat) (i : Nat) : Nat :=
  fld(F (Nat.shiftRight i (nat_lit 4)), Nat.mul (nat_lit 64) (Nat.land i (nat_lit 15)),
    nat_lit 18446744073709551615)

@[expose] noncomputable def wv (T : Nat → Nat → Nat) (w : List Nat) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) y (fun c _ ih => strictN ih (T c)) w

@[expose] noncomputable def fpar (e : Nat) : Nat := Nat.land e (nat_lit 32767)

@[expose] noncomputable def fgen (e : Nat) : Nat := fld(e, nat_lit 15, nat_lit 3)

@[expose] noncomputable def ford (e : Nat) : Nat := fld(e, nat_lit 17, nat_lit 32767)

@[expose] noncomputable def frt (e : Nat) : Nat := Nat.shiftRight e (nat_lit 32)

@[expose] noncomputable def fOK (n : Nat) (FE : Nat → Nat) (G : Nat → Nat → Nat) (R : Nat → Nat)
    (p : Nat) : Bool :=
  strictB (FE p) fun e => bIf(Nat.beq (R (frt e)) p, true,
    strictB (fpar e) fun q => bAnd(Nat.blt q n, strictB (FE q) fun e' =>
      bAnd(Nat.blt (ford e') (ford e), bAnd(Nat.beq (frt e') (frt e),
        Nat.beq (G (fgen e) q) p))))

@[expose] noncomputable def relPt (T : Nat → Nat → Nat) (rs : List (List Nat)) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(Nat.beq (wv T r y) y, ih)) rs

@[expose] noncomputable def baseEq (T : Nat → Nat → Nat) (b : Nat) (w v : List Nat) : Bool :=
  bAnd(Nat.beq (wv T w (nat_lit 0)) (wv T v (nat_lit 0)), Nat.beq (wv T w b) (wv T v b))

@[expose] noncomputable def sortedB : List Nat → Bool
  | [] => true
  | x :: l => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun y _ ih x => bAnd(Nat.blt x y, ih y)) l x

@[expose] noncomputable def memB (m x : Nat) : Bool := Nat.beq fld(m, x, nat_lit 1) (nat_lit 1)

@[expose] noncomputable def maskOf {α : Type} (l : List (Nat × α)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) r.1)) l

end CFSG.KC.J3C

end
