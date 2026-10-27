module

public import Certificates.Data.Kernel.U6.Abar

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def imgSet (P m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p acc => strictN acc fun acc =>
      nIf(Nat.beq (fget m p (nat_lit 1)) (nat_lit 1), Nat.lor acc (pw2 (ap10 P p)), acc))
    (nat_lit 693)

@[expose] noncomputable def recPar (RP j : Nat) : Nat := Nat.land (fget RP j (nat_lit 16)) (nat_lit 1023)

@[expose] noncomputable def recLet (RP j : Nat) : Nat :=
  Nat.shiftRight (fget RP j (nat_lit 16)) (nat_lit 10)

@[expose] noncomputable def recSets (LT FA RP n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc fun acc =>
      Nat.lor acc (Nat.shiftLeft
        (nIf(Nat.beq j (nat_lit 0), FA,
          imgSet (letK LT (recLet RP j)) (fget acc (recPar RP j) (nat_lit 693))))
        (Nat.mul (nat_lit 693) j)))
    n

@[expose] noncomputable def fixAK3 (A FA : Nat) : Bool :=
  strictB (evW A [nat_lit 0, nat_lit 2, nat_lit 8]) fun j =>
    andB (allBelow (nat_lit 693) (nat_lit 11) fun p =>
        Bool.rec (Nat.beq (fget FA p (nat_lit 1)) (nat_lit 0))
          (Nat.beq (fget FA p (nat_lit 1)) (nat_lit 1)) (Nat.beq (ap10 j p) p))
      (allN (nat_lit 9) fun i => strictB (elt A i) fun a =>
        allBelow (nat_lit 693) (nat_lit 11) fun p =>
          orB (Nat.beq (fget FA p (nat_lit 1)) (nat_lit 0)) (Nat.beq (ap10 a p) p))

@[expose] noncomputable def transK (LT FA RP SO n : Nat) : Bool :=
  strictB (recSets LT FA RP n) fun X =>
    andB (allN n fun j => orB (Nat.beq j (nat_lit 0))
        (andB (Nat.blt (recPar RP j) j) (Nat.blt (recLet RP j) (nat_lit 46))))
      (andB (allN n fun i => Nat.blt (fget SO i (nat_lit 10)) n)
        (allN (Nat.sub n (nat_lit 1)) fun i =>
          Nat.blt (fget X (fget SO i (nat_lit 10)) (nat_lit 693))
            (fget X (fget SO (Nat.succ i) (nat_lit 10)) (nat_lit 693))))

end CFSG.KC.U6

end
