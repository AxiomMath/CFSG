module

public import Certificates.Data.Kernel.Spor.Fi24Orb

public section

namespace CFSG.KC.Fi24G2e

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb

@[expose] def zWord (w g : List Nat) : List Nat := w ++ g.reverse ++ w ++ g

@[expose] def brayWord (w g : List Nat) (e : Nat) (odd : Bool) : List Nat :=
  (if odd then g else []) ++ (List.replicate e (zWord w g)).flatten

@[expose] noncomputable def iterWalk (TG : Nat → Nat → Nat) (z : List Nat) (e r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) r (fun _ acc => strictN acc (fun s => walk TG z s)) e

@[expose] noncomputable def brayWalk (TG : Nat → Nat → Nat) (w g : List Nat) (e : Nat) (odd : Bool)
    (r : Nat) : Nat :=
  iterWalk TG (zWord w g) e (Bool.rec (motive := fun _ => Nat) r (walk TG g r) odd)

@[expose] noncomputable def permLOK (FL : Nat → Nat) (f : Nat → Nat) (P : Nat → Nat) (m : Nat) : Bool :=
  allBelow m (nat_lit 16) (fun i => andB (Nat.blt (P i) m) (Nat.beq (f (FL i)) (FL (P i))))

@[expose] noncomputable def invLOK (P Q : Nat → Nat) (m : Nat) : Bool :=
  allBelow m (nat_lit 16) (fun i => andB (Nat.blt (Q i) m) (Nat.beq (P (Q i)) i))

@[expose] noncomputable def cmLOK (A Ai B Bi C : Nat → Nat) (m : Nat) : Bool :=
  allBelow m (nat_lit 16) (fun i => Nat.beq (C i) (Bi (Ai (B (A i)))))

@[expose] noncomputable def cntId (P : Nat → Nat) (m : Nat) : Nat :=
  sumBelow m (nat_lit 16) (fun i => nIf(Nat.beq (P i) i, nat_lit 1, nat_lit 0))

@[expose] noncomputable def clStep (FL : Nat → Nat) (TG : Nat → Nat → Nat) (QL : Nat → List Nat)
    (YL : Nat → Nat) (o u0 u1 u2 m j : Nat) : Bool :=
  letB (FL j) (fun x => orB (Nat.beq x u0) (orB (Nat.beq x u1) (orB (Nat.beq x u2)
    (andB (Nat.beq (walk TG (QL j) o) x) (andB (Nat.blt (YL j) m)
      (letB (FL (YL j)) (fun y => bIf(Nat.beq (walk TG ((QL j).reverse ++ 0 :: QL j) y) y,
        false, true))))))))

@[expose] noncomputable def clauseOK (FL : Nat → Nat) (TG : Nat → Nat → Nat) (QL : Nat → List Nat)
    (YL : Nat → Nat) (o u0 u1 u2 m : Nat) : Bool :=
  allBelow m (nat_lit 16) (fun j => clStep FL TG QL YL o u0 u1 u2 m j)

end CFSG.KC.Fi24G2e

end
