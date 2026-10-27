module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.LceS

public section

namespace CFSG.KC.Fi24FixK

open CFSG.KC.Loop CFSG.KC.LceS

@[expose] noncomputable def walk (TG : Nat → Nat → Nat) (w : List Nat) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun r => r) (fun g _ ih r => strictN (TG g r) ih) w r

@[expose] noncomputable def cl1 (S IX : Nat → Nat) (n i g y : Nat) : Bool :=
  letB (IX (Nat.add (Nat.mul (nat_lit 9) i) g)) (fun j => andB (Nat.blt j n) (Nat.beq (S j) y))

@[expose] noncomputable def cl9 (S IX : Nat → Nat) (TG : Nat → Nat → Nat) (n i a : Nat) : Bool :=
  andB (cl1 S IX n i (nat_lit 0) (TG (nat_lit 1) a)) (andB (cl1 S IX n i (nat_lit 1) (TG (nat_lit 2) a))
  (andB (cl1 S IX n i (nat_lit 2) (TG (nat_lit 3) a)) (andB (cl1 S IX n i (nat_lit 3) (TG (nat_lit 4) a))
  (andB (cl1 S IX n i (nat_lit 4) (TG (nat_lit 5) a)) (andB (cl1 S IX n i (nat_lit 5) (TG (nat_lit 6) a))
  (andB (cl1 S IX n i (nat_lit 6) (TG (nat_lit 7) a)) (andB (cl1 S IX n i (nat_lit 7) (TG (nat_lit 8) a))
    (cl1 S IX n i (nat_lit 8) (TG (nat_lit 10) a)))))))))

@[expose] noncomputable def closOK (S IX : Nat → Nat) (TG : Nat → Nat → Nat) (n lo m hi : Nat) :
    Bool :=
  allBelow m hi (fun t => letB (Nat.add lo t) (fun i => letB (S i) (fun s =>
    letB (TG (nat_lit 0) s) (fun a => cl9 S IX TG n i a))))

@[expose] noncomputable def cntFix (S : Nat → Nat) (TG : Nat → Nat → Nat) (w u : List Nat)
    (lo m hi : Nat) : Nat :=
  sumBelow m hi (fun t => strictN (S (Nat.add lo t)) (fun s => strictN (walk TG w s) (fun y =>
    nIf(Nat.beq (walk TG u y) y, nat_lit 1, nat_lit 0))))

@[expose] noncomputable def D81 : Nat :=
  0xa3468d1a2f5e3b74e5c376cd5a3364c582f5cb562b54a54274c95251a3468d1a28d121407cf1d386cd19305cb15284c911203c70d182c551a13e74d992c4880e18284060808095264478d16243a30a0c07f45f51a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1

@[expose] noncomputable def d81 (c : Nat) : Nat := fld(D81, Nat.mul (nat_lit 7) c, nat_lit 127)

@[expose] noncomputable def digitsOK (CT : Nat → Nat) (len : Nat) (cs : List Char) (t : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun t => Nat.beq t len)
    (fun ch _ ih t => andB (Nat.beq (CT t) (d81 ch.toNat)) (letB (Nat.succ t) ih)) cs t

@[expose] noncomputable def bitAt (z o : Nat) : Nat := fld(z, o, nat_lit 1)

@[expose] noncomputable def entOK (z1 z2 o v : Nat) : Bool :=
  andB (Nat.beq (bitAt z1 o) (nIf(Nat.beq v (nat_lit 1), nat_lit 1, nat_lit 0)))
    (Nat.beq (bitAt z2 o) (nIf(Nat.beq v (nat_lit 2), nat_lit 1, nat_lit 0)))

@[expose] noncomputable def trit (x s : Nat) : Nat :=
  Nat.mod (Nat.div x (nIf(Nat.beq s (nat_lit 0), nat_lit 1, nIf(Nat.beq s (nat_lit 1), nat_lit 3,
    nIf(Nat.beq s (nat_lit 2), nat_lit 9, nat_lit 27))))) (nat_lit 3)

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 781)) (nat_lit 1)

@[expose] noncomputable def colsOK (P1 P2 : Nat) (CT : Nat → Nat) : Bool :=
  allBelow (nat_lit 528) (nat_lit 9) (fun j =>
    letB (Nat.mul (nat_lit 781) (Nat.add (nat_lit 253) j)) (fun o =>
    letB (Nat.land (Nat.shiftRight P1 o) RM) (fun r1 =>
    letB (Nat.land (Nat.shiftRight P2 o) RM) (fun r2 =>
      allBelow (nat_lit 253) (nat_lit 4) (fun i => entOK r1 r2 i
        (trit (CT (Nat.add (Nat.mul (nat_lit 132) i) (Nat.div j (nat_lit 4)))) (Nat.mod j (nat_lit 4))))))))

@[expose] noncomputable def rowsZOK (P1 P2 : Nat) : Bool :=
  allBelow (nat_lit 781) (nat_lit 13) (fun j =>
    letB (Nat.land (Nat.shiftRight P1 (Nat.mul (nat_lit 781) j)) RM) (fun r1 =>
    letB (Nat.land (Nat.shiftRight P2 (Nat.mul (nat_lit 781) j)) RM) (fun r2 =>
      bIf(Nat.blt j (nat_lit 253),
        andB (Nat.beq r1 (Nat.shiftLeft (nat_lit 1) j)) (Nat.beq r2 (nat_lit 0)),
        andB (Nat.beq (Nat.shiftRight r1 (nat_lit 253)) (nat_lit 0))
          (Nat.beq (Nat.shiftRight r2 (nat_lit 253)) (nat_lit 0))))))

end CFSG.KC.Fi24FixK

end
