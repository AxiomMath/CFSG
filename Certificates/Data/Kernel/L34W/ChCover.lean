module

public import Certificates.Data.Kernel.L34W.Model
public import Certificates.Data.ChengHeldCover

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.OddStandard.ChengHeldData

@[expose] noncomputable def evalC (T : Nat → Nat) (σ : Nat → Nat) (t : Tm) : Nat :=
  Tm.rec (motive := fun _ => Nat) (fun i => σ i) (nat_lit 0) (fun _ _ a b => mulC T a b)
    (fun _ a => invC T a) t

@[expose] noncomputable def inKN (c1 c2 i j : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun m ih => Bool.rec (motive := fun _ => Bool) ih true
      (bAnd(Nat.beq (Nat.mod (Nat.mul m c1) (nat_lit 4)) i,
        Nat.beq (Nat.mod (Nat.mul m c2) (nat_lit 4)) j))) (nat_lit 4)

@[expose] noncomputable def subM (a b : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add a (nat_lit 4)) b) (nat_lit 4)

@[expose] noncomputable def eqKC (c1 c2 x y : Nat) : Bool :=
  bAnd(Nat.beq (Nat.div x (nat_lit 16)) (Nat.div y (nat_lit 16)),
    inKN c1 c2 (subM (Nat.mod (Nat.div x (nat_lit 4)) (nat_lit 4))
        (Nat.mod (Nat.div y (nat_lit 4)) (nat_lit 4)))
      (subM (Nat.mod x (nat_lit 4)) (Nat.mod y (nat_lit 4))))

@[expose] noncomputable def eqN2C (x y : Nat) : Bool :=
  bAnd(Nat.beq (Nat.div x (nat_lit 16)) (Nat.div y (nat_lit 16)),
    Nat.beq (Nat.mod x (nat_lit 2)) (Nat.mod y (nat_lit 2)))

@[expose] noncomputable def relsC (T : Nat → Nat) (E : Nat → Nat → Bool) (σ : Nat → Nat)
    (rels : List (Tm × Tm)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(E (evalC T σ e.1) (evalC T σ e.2), ih)) rels

@[expose] noncomputable def actC (T A : Nat → Nat) (E : Nat → Nat → Bool) (σ : Nat → Nat) (i : Nat)
    (rels : List (Nat × Tm)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(E (betaRepC A i (σ e.1)) (evalC T σ e.2), ih)) rels

@[expose] noncomputable def frC (α i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), nIf(Nat.beq α (nat_lit 1), nat_lit 3, nat_lit 1),
  nIf(Nat.beq i (nat_lit 1), nIf(Nat.beq α (nat_lit 2), nat_lit 65, nat_lit 67),
  nIf(Nat.beq i (nat_lit 2), nIf(Nat.beq α (nat_lit 0), nat_lit 131, nat_lit 129),
  nIf(Nat.beq i (nat_lit 3), nat_lit 48,
  nIf(Nat.beq i (nat_lit 4), nat_lit 32,
  nIf(Nat.beq i (nat_lit 5), nat_lit 384, nat_lit 256))))))

end CFSG.KC.L34W

end
