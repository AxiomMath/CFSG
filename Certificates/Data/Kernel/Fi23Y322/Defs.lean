module

public import Certificates.Data.Kernel.Fi23Five.Defs

public section

namespace CFSG.KC.Fi23Y322

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five

@[expose] noncomputable def tW (G : Nat → Nat) (u : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun k _ ih => strictN ih (tA G k)) u

@[expose] noncomputable def idK (G : Nat → Nat) (u : List Nat) : Bool :=
  allN (nat_lit 6) fun b => Nat.beq (tW G u b) b

@[expose] noncomputable def fixL (G : Nat → Nat) (w : List Nat) (ks : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun k _ ih => bAnd(Nat.blt k (nat_lit 31671), bAnd(Nat.beq (wv G w k) k, ih))) ks

@[expose] noncomputable def wordsK (G : Nat → Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun u _ ih => bAnd(idK G u, ih)) W

@[expose] noncomputable def yK (G : Nat → Nat) (w ks : List Nat) (W : List (List Nat))
    (a b : Nat) : Bool :=
  bAnd(fixL G w ks, bAnd(wordsK G W, Bool.not (cmK G a b)))

end CFSG.KC.Fi23Y322

end
