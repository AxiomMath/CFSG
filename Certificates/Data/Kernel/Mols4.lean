module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.Mols4

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def pc (PL i : Nat) : Nat := fget PL i (nat_lit 8)

@[expose] noncomputable def img (c y : Nat) : Nat := fget c y (nat_lit 2)

@[expose] noncomputable def sel (t x : Nat) : Nat :=
  Nat.mod (Nat.div t (Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun _ ih => Nat.mul (nat_lit 24) ih) x))
    (nat_lit 24)

@[expose] noncomputable def ent (PL t x y : Nat) : Nat :=
  nIf(Nat.beq x (nat_lit 0), y, img (pc PL (sel t (Nat.sub x (nat_lit 1)))) y)

@[expose] noncomputable def permsOK (PL : Nat) : Bool :=
  andB (allN (nat_lit 24) fun i => Nat.beq (orN (nat_lit 4) fun y => pw2 (img (pc PL i) y)) (nat_lit 15))
    (Nat.beq (popc (nat_lit 256) (orN (nat_lit 24) fun i => pw2 (pc PL i))) (nat_lit 24))

@[expose] noncomputable def latinT (PL t : Nat) : Bool :=
  allN (nat_lit 4) fun y => Nat.beq (orN (nat_lit 4) fun x => pw2 (ent PL t x y)) (nat_lit 15)

@[expose] noncomputable def orthT (PL t u : Nat) : Bool :=
  Nat.beq (orN (nat_lit 16) fun c =>
      (fun x y => pw2 (Nat.add (Nat.mul (nat_lit 4) (ent PL t x y)) (ent PL u x y)))
        (Nat.div c (nat_lit 4)) (Nat.mod c (nat_lit 4)))
    (nat_lit 65535)

@[expose] noncomputable def lt (LL i : Nat) : Nat := fget LL i (nat_lit 14)

@[expose] noncomputable def listOK (PL LL : Nat) : Bool :=
  andB (allN (nat_lit 24) fun i => latinT PL (lt LL i))
  (andB (allN (nat_lit 23) fun i => Nat.blt (lt LL i) (lt LL (Nat.succ i)))
  (andB (Nat.blt (lt LL (nat_lit 23)) (nat_lit 13824))
    (Nat.beq (sumBelow (nat_lit 13824) (nat_lit 216) fun t => nIf(latinT PL t, nat_lit 1, nat_lit 0))
      (nat_lit 24))))

@[expose] noncomputable def molsK (PL LL tA tB tC : Nat) : Bool :=
  allN (nat_lit 24) fun a => (fun r₂ =>
    orB (notB (allN (nat_lit 3) fun x => Nat.beq (img (pc PL (sel r₂ x)) (nat_lit 0)) (Nat.succ x)))
      (allN (nat_lit 24) fun b => (fun r₃ =>
        orB (notB (orthT PL r₂ r₃))
          (allN (nat_lit 24) fun c => (fun r₄ =>
            orB (notB (andB (orthT PL r₂ r₄) (orthT PL r₃ r₄)))
              (andB (Nat.beq r₂ tA) (orB (andB (Nat.beq r₃ tB) (Nat.beq r₄ tC))
                (andB (Nat.beq r₃ tC) (Nat.beq r₄ tB))))) (lt LL c))) (lt LL b))) (lt LL a)

end CFSG.KC.Mols4

end
