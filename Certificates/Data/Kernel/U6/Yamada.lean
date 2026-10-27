module

public import Certificates.Data.Kernel.U6.Perm

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def commP (p q : Nat) : Bool := Nat.beq (pc p q) (pc q p)

@[expose] noncomputable def commutP (a k : Nat) : Nat := pc (pc (pc a k) (invP a)) (invP k)

@[expose] noncomputable def commK (A K : Nat) : Bool :=
  strictB (elt A (nat_lit 0)) fun j1 =>
  strictB (evW A [nat_lit 2, nat_lit 8]) fun j2 =>
  strictB (evW K [nat_lit 4]) fun k1 =>
  strictB (evW K [nat_lit 0, nat_lit 4, nat_lit 0, nat_lit 4, nat_lit 1, nat_lit 4, nat_lit 1]) fun k2 =>
    andB (commP k1 j1)
    (andB (Nat.beq (commutP (evW A [nat_lit 2, nat_lit 4]) k1) j1)
    (andB (commP k2 j2)
      (Nat.beq (commutP (evW A [nat_lit 4, nat_lit 10]) k2) j2)))

@[expose] noncomputable def transCore (K O j1 : Nat) (sW : List (List Nat)) : Bool :=
  andB (allN (nat_lit 6) fun t =>
      strictB (nIf(Nat.blt t (nat_lit 3), elt K t, invP (elt K (Nat.sub t (nat_lit 3))))) fun g =>
        allN (nat_lit 21) fun i => strictB (conjP g (elt O i)) fun x =>
          anyN (nat_lit 21) fun j => Nat.beq x (elt O j))
    (strictB (evList K sW) fun SW =>
      allN (nat_lit 21) fun m => orB (Nat.beq m (nat_lit 0))
        (strictB (elt SW m) fun s =>
          andB (commP s j1) (Nat.beq (conjP s (elt O (nat_lit 1))) (elt O m))))

@[expose] noncomputable def check3000 (LT : Nat) (aW kW oW sW : List (List Nat)) : Bool :=
  strictB (evList LT aW) fun A => strictB (evList LT kW) fun K =>
  strictB (elt A (nat_lit 0)) fun j1 =>
  strictB (evList K oW) fun G =>
  strictB (orN (nat_lit 21) fun i => Nat.shiftLeft (conjP (elt G i) j1) (Nat.mul (nat_lit 6930) i)) fun O =>
    andB (commK A K) (transCore K O j1 sW)

@[expose] noncomputable def tvP (UP POS p : Nat) : Nat :=
  strictN (up UP p) fun v => sumBelow (nat_lit 693) (nat_lit 11) fun q =>
    Nat.shiftLeft (tabK UP POS v q) (Nat.mul (nat_lit 10) q)

@[expose] noncomputable def check3004 (UP POS LT BT : Nat) (aW : List (List Nat)) : Bool :=
  strictB (evList LT aW) fun A =>
  strictB (orN (nat_lit 21) fun i => Nat.shiftLeft (tvP UP POS (fget BT i (nat_lit 10)))
    (Nat.mul (nat_lit 6930) i)) fun T =>
    andB (allN (nat_lit 9) fun g => anyN (nat_lit 21) fun i => Nat.beq (elt A g) (elt T i))
      (Nat.beq (elt A (nat_lit 0)) (elt T (nat_lit 5)))

end CFSG.KC.U6

end
