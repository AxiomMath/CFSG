module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.L5E16

open CFSG.KC.Enum

@[expose] noncomputable def mul16 (p q : Nat) : Nat :=
  pcomp (nat_lit 16) (nat_lit 5) (nat_lit 31) p q

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a x, true, ih)) L

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) L

@[expose] noncomputable def closedK (one : Nat) (S G : List Nat) : Bool :=
  bAnd(memK one S, allL S fun s => allL G fun g => memK (mul16 s g) S)

@[expose] noncomputable def invB (one u : Nat) : Bool :=
  bAnd(Bool.not (Nat.beq u one), Nat.beq (mul16 u u) one)

@[expose] noncomputable def cmI (one t u : Nat) : Bool :=
  bAnd(invB one u, Nat.beq (mul16 t u) (mul16 u t))

@[expose] noncomputable def cntK (one : Nat) (S : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun u _ ih => nIf(cmI one t u, Nat.succ ih, ih)) S

@[expose] noncomputable def e16K (one : Nat) (S R : List Nat) : Bool :=
  allL S fun t => bIf(bAnd(invB one t, Bool.not (memK t R)), Nat.blt (cntK one S t) (nat_lit 15),
    true)

end CFSG.KC.L5E16

end
