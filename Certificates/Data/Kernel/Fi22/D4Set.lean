module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Fi22D4

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def packL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.add a (Nat.shiftLeft ih (nat_lit 12))) l

@[expose] noncomputable def ltL (l : List Nat) (b : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(Nat.blt a b, ih)) l

@[expose] noncomputable def f12 (O k : Nat) : Nat := pg (nat_lit 12) (mask (nat_lit 12)) O k

@[expose] noncomputable def f9 (Q k : Nat) : Nat := pg (nat_lit 9) (mask (nat_lit 9)) Q k

@[expose] noncomputable def bijK (O Q : Nat) : Bool :=
  allN (nat_lit 360) fun k =>
    bAnd(Nat.blt (f12 O k) (nat_lit 3510), Nat.beq (f9 Q (f12 O k)) k)

@[expose] noncomputable def inK (O Q q : Nat) : Bool :=
  bAnd(Nat.blt (f9 Q q) (nat_lit 360), Nat.beq (f12 O (f9 Q q)) q)

@[expose] noncomputable def presK (O Q T : Nat) : Bool :=
  allN (nat_lit 360) fun k => inK O Q (f12 T (f12 O k))

@[expose] noncomputable def outK (O Q T : Nat) : Bool :=
  bIf(allN (nat_lit 360) (fun k => Nat.blt (f9 Q (f12 T (f12 O k))) (nat_lit 360)), false, true)

@[expose] noncomputable def resK (O R T : Nat) : Bool :=
  allN (nat_lit 360) fun k =>
    bAnd(Nat.blt (f9 R k) (nat_lit 360), Nat.beq (f12 O (f9 R k)) (f12 T (f12 O k)))

@[expose] noncomputable def itK (T k p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => f12 T q) k

@[expose] noncomputable def faithK (O X Y : Nat) : Bool :=
  allN (nat_lit 5) fun i => allN (nat_lit 5) fun j =>
    bIf(bAnd(Nat.beq i (nat_lit 0), Nat.beq j (nat_lit 0)), true,
      bIf(allN (nat_lit 360) (fun k => Nat.beq (itK X i (itK Y j (f12 O k))) (f12 O k)),
        false, true))

end CFSG.KC.Fi22D4

end
