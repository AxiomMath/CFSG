module

public import Certificates.Data.Kernel.Fi23Five.Defs

public section

namespace CFSG.KC.Fi23Cls

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Five

@[expose] noncomputable def cntL (q : Nat → Bool) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r _ ih => strictN ih fun n => nIf(q r, Nat.succ n, n)) L

@[expose] noncomputable def valF (G : Nat → Nat) (p r : Nat) : Bool :=
  bAnd(Bool.not (Nat.beq r p), cmK G p r)

@[expose] noncomputable def ord3K (G : Nat → Nat) (w : List Nat) : Bool :=
  allN (nat_lit 6) fun t => Nat.beq (wv G w (wv G w (wv G w t))) t

@[expose] noncomputable def stepD (G : Nat → Nat) (w : List Nat) (p r s : Nat) : Bool :=
  bIf(Nat.beq r p, true, bIf(cmK G p r,
    bAnd(Nat.blt s (nat_lit 31671), bAnd(Nat.beq (wv G w s) s,
      bAnd(Bool.not (cmK G p s), Bool.not (cmK G s r)))), true))

@[expose] noncomputable def diamK (G : Nat → Nat) (w : List Nat) (p : Nat) (L : List Nat) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun r _ ih S => List.rec (motive := fun _ => Bool) false
      (fun s S' _ => bAnd(stepD G w p r s, ih S')) S) L

@[expose] noncomputable def clsK (G : Nat → Nat) (w : List Nat) (p N V : Nat) (L S : List Nat) :
    Bool :=
  bAnd(ord3K G w, bAnd(Nat.blt p (nat_lit 31671), bAnd(Nat.beq (wv G w p) p,
    bAnd(Nat.beq (cntL (fun _ => true) L) N, bAnd(Nat.beq (cntL (valF G p) L) V,
      diamK G w p L S)))))

end CFSG.KC.Fi23Cls

end
