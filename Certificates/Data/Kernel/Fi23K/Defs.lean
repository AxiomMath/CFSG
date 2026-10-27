module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Fi23K

open CFSG.KC.Enum

@[expose] noncomputable def tb (G : Nat → Nat) (r x : Nat) : Nat :=
  strictN (Nat.add (Nat.mul r (nat_lit 495)) (Nat.shiftRight x (nat_lit 6))) fun k =>
    fld(G k, Nat.mul (nat_lit 15) (Nat.land x (nat_lit 63)), nat_lit 32767)

@[expose] noncomputable def wv (G : Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun r _ ih => tb G r ih) w

@[expose] noncomputable def eqAt (G : Nat → Nat) (l r : List Nat) (x : Nat) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true (fun h _ _ => Nat.blt (tb G h x) (nat_lit 31671)) l,
    Nat.beq (wv G l x) (wv G r x))

@[expose] noncomputable def eqSl (G : Nat → Nat) (EL ER : Nat → List Nat) (k0 nk lo c : Nat) :
    Bool :=
  allN c fun i => strictB (Nat.add lo i) fun x => bIf(Nat.blt x (nat_lit 31671),
    allN nk (fun j => strictB (Nat.add k0 j) fun k => eqAt G (EL k) (ER k) x), true)

end CFSG.KC.Fi23K

end
