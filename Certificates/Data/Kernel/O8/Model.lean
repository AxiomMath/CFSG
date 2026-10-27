module

public import Certificates.Data.Kernel.O8.CPM

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw
open CFSG.KC.Enum (pidn pcomp permOK pg)

structure ChainK where
  LR : Nat → Nat
  TRI : Nat → Nat
  BP : Nat
  nb : Nat

@[expose] noncomputable def siftCh (n w : Nat) (c : ChainK) (g : Nat) : Bool :=
  siftC n w c.LR c.TRI c.BP c.nb g

@[expose] noncomputable def conjPK (n w g gi x : Nat) : Nat := pc n w (pc n w g x) gi

@[expose] noncomputable def basicOK (n w : Nat) (PSI PA PAI UA UAI : Nat → Nat) (G UR : Nat)
    (cL cP cU : ChainK) : Bool :=
  andB (allN (nat_lit 64) fun y => (fun P => andB (permOK n w (mask w) (Nat.mul n w) P P)
      (andB (siftCh n w cL P) (andB (siftCh n w cP P) (siftCh n w cU P)))) (PSI y))
    (andB (allN (nat_lit 64) fun y => allN (nat_lit 64) fun y' =>
        andB (Nat.beq (PSI (Nat.xor y y')) (pc n w (PSI y) (PSI y')))
          (orB (Nat.beq y y') (notB (Nat.beq (PSI y) (PSI y')))))
      (andB (allN (nat_lit 6) fun i => andB (permOK n w (mask w) (Nat.mul n w) (PA i) (PAI i))
          (andB (siftCh n w cL (PA i)) (allN (nat_lit 64) fun y =>
            Nat.beq (conjPK n w (PA i) (PAI i) (PSI y)) (PSI (bvecK (mat G i) y)))))
        (andB (allN (nat_lit 6) fun k => andB (permOK n w (mask w) (Nat.mul n w) (UA k) (UAI k))
            (andB (siftCh n w cL (UA k)) (allN (nat_lit 64) fun y =>
              Nat.beq (conjPK n w (UA k) (UAI k) (PSI y)) (PSI (bvecK (mat UR k) y)))))
          (allN (nat_lit 64) fun y => orB (notB (allN (nat_lit 6) fun k =>
              Nat.beq (bvecK (mat UR k) y) y)) (orB (Nat.beq y (nat_lit 0)) (Nat.beq y (nat_lit 1)))))))

end CFSG.KC.O8

end
