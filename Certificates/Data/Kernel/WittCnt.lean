module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.WCnt

open CFSG.KC.Enum

@[expose] noncomputable def cRow (n w m : Nat) (c : Nat → Bool) (k : Nat → Nat → Nat) (g : Nat) :
    List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun t _ ih acc => strictN (pcomp n w m g t) (fun h =>
      nIf(c h, strictN (k h acc) ih, ih acc)))

@[expose] noncomputable def ccnt (n w m : Nat) (F : Nat → Nat) :
    List ((Nat → Bool) × List Nat) → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun g acc => Nat.add acc (F g))
    (fun L _ ih g acc => cRow n w m L.1 ih g L.2 acc)

@[expose] noncomputable def pt (x i : Nat) : Nat := fld(x, Nat.mul (nat_lit 5) i, nat_lit 31)

@[expose] noncomputable def inM (X x : Nat) : Bool := Nat.beq fld(X, x, nat_lit 1) (nat_lit 1)

@[expose] noncomputable def upk22 (x : Nat) (i : Fin 22) : Fin 22 :=
  ⟨Nat.mod (pt x i.val) (nat_lit 22), Nat.mod_lt _ (by decide)⟩

@[expose] noncomputable def ind (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q] (D x : Nat) :
    Nat :=
  strictN (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) x D) (fun y =>
    nIf(decide (Q (upk22 y)), nat_lit 1, nat_lit 0))

@[expose] noncomputable def indB (b : Nat → Bool) (D x : Nat) : Nat :=
  strictN (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) x D) (fun y => nIf(b y, nat_lit 1, nat_lit 0))

@[expose] noncomputable def allB (f : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n

@[expose] noncomputable def presT (X : Nat) (l : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun i _ ih => bAnd(inM X (pt y i), ih)) l

@[expose] noncomputable def relT (T P y : Nat) : Bool :=
  allB (fun i => Nat.beq (pt y (pt T i)) (pt P (pt y i))) (nat_lit 22)

@[expose] noncomputable def relAny (T : Nat) (Ps : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun P _ ih => bIf(relT T P y, true, ih)) Ps

end CFSG.KC.WCnt

end
