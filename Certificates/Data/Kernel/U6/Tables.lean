module

public import Certificates.Data.Kernel.U6.Perm
public import Certificates.Data.Kernel.S23Inner

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.KC.S23 (par)

@[expose] noncomputable def EV : Nat := nat_lit 1365

@[expose] noncomputable def hermB (x v : Nat) : Nat :=
  (fun x0 x1 v1 => (fun c0 => (fun p0 p1 => Nat.add (par p0) (Nat.mul (nat_lit 2) (par p1)))
      (Nat.xor (Nat.land x0 c0) (Nat.land x1 v1))
      (Nat.xor (Nat.xor (Nat.land x0 v1) (Nat.land x1 c0)) (Nat.land x1 v1)))
    (Nat.xor (Nat.land v EV) v1))
  (Nat.land x EV) (Nat.land (Nat.shiftRight x (nat_lit 1)) EV) (Nat.land (Nat.shiftRight v (nat_lit 1)) EV)

@[expose] noncomputable def posnOK (POS POSN : Nat) : Bool :=
  allBelow (nat_lit 4096) (nat_lit 64) fun c => Nat.beq (fget POSN c (nat_lit 10)) (pos POS (normK c))

@[expose] noncomputable def mvOK (UP MVT : Nat) : Bool :=
  allBelow (nat_lit 693) (nat_lit 11) fun m => allN (nat_lit 4) fun a =>
    Nat.beq (fget MVT (Nat.add (Nat.mul (nat_lit 4) m) a) (nat_lit 12)) (scaleK a (up UP m))

@[expose] noncomputable def rowOK (UP POSN MVT : Nat) (R : Nat → Nat) (m : Nat) : Bool :=
  strictB (R m) fun Rm => strictB (up UP m) fun v =>
    andB (Nat.beq (Nat.shiftRight Rm (nat_lit 6930)) (nat_lit 0))
      (allBelow (nat_lit 693) (nat_lit 11) fun q => strictB (up UP q) fun x =>
        Nat.beq (fget Rm q (nat_lit 10))
          (fget POSN (Nat.xor x (fget MVT (Nat.add (Nat.mul (nat_lit 4) m) (hermB x v)) (nat_lit 12)))
            (nat_lit 10)))

@[expose] noncomputable def rowsOK (UP POSN MVT : Nat) (R : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt fun i => rowOK UP POSN MVT R (Nat.add lo i)

@[expose] noncomputable def swapK (R : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt fun i => (fun p => strictB (R p) fun Rp =>
    allBelow (nat_lit 693) (nat_lit 11) fun q => strictB (fget Rp q (nat_lit 10)) fun t =>
      orB (Nat.beq t q) (Nat.beq t (fget (R q) p (nat_lit 10)))) (Nat.add lo i)

@[expose] noncomputable def maskL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor (pw2 x) ih) l

@[expose] noncomputable def fixAK (R : Nat → Nat) (FA : Nat) : Bool :=
  allBelow (nat_lit 693) (nat_lit 11) fun m => orB (bit FA m) (strictB (R m) fun Rm =>
    anyN (nat_lit 693) fun q => andB (bit FA q) (notB (bit FA (fget Rm q (nat_lit 10)))))

@[expose] noncomputable def j1K (LT : Nat) (R : Nat → Nat) (aW : List (List Nat)) : Bool :=
  strictB (evList LT aW) fun A => Nat.beq (elt A (nat_lit 0)) (R (nat_lit 0))

end CFSG.KC.U6

end
