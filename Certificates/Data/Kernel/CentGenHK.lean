module

public import Certificates.Data.Kernel.CentGenK

public section

namespace CFSG.KC.CentGenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

@[expose] noncomputable def nielOK (prog : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => bAnd(Nat.beq (opC r) (nat_lit 0), bAnd(Nat.blt (opK r) (nat_lit 2),
      bAnd(Nat.beq (Nat.add (opA r) (opB r)) (nat_lit 1), ih)))) prog

structure HPK where
  p : Nat
  prog : List Nat
  ke : Nat
  kf : Nat

@[expose] noncomputable def finHK (n w m idn : Nat) (D : HPK) (R : List Nat) : Bool :=
  strictB (MOC.powK n w m idn (getR idn R (nat_lit 0)) D.ke) (fun x =>
  strictB (MOC.powK n w m idn (getR idn R (nat_lit 1)) D.kf) (fun y =>
  strictB (pcomp n w m (pcomp n w m (pcomp n w m x y)
    (MOC.powK n w m idn x (Nat.sub D.p (nat_lit 1)))) (MOC.powK n w m idn y (Nat.sub D.p (nat_lit 1))))
    (fun z =>
  bAnd(Nat.blt (nat_lit 0) D.p,
  bAnd(Nat.beq (MOC.powK n w m idn x D.p) idn,
  bAnd(Nat.beq (MOC.powK n w m idn y D.p) idn,
  bAnd(Nat.beq (pcomp n w m z x) (pcomp n w m x z),
  bAnd(Nat.beq (pcomp n w m z y) (pcomp n w m y z),
  bAnd(neAll n w m z x D.p idn, neAll n w m z y D.p idn)))))))))

@[expose] noncomputable def hpK (n w A B : Nat) (D : HPK) : Bool :=
  strictB (mask w) (fun m => strictB (Nat.mul n w) (fun nw => strictB (pidn n w) (fun idn =>
  bAnd(szOK n w,
  bAnd(Nat.beq (Nat.shiftRight A nw) (nat_lit 0),
  bAnd(Nat.beq (Nat.shiftRight B nw) (nat_lit 0),
  bAnd(nielOK D.prog,
  runK n w m nw idn (nat_lit 2) [] D.prog (finHK n w m idn D) (initR A B (nat_lit 0) idn))))))))

end CFSG.KC.CentGenK

end
