module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KC.CentGenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

@[expose] noncomputable def opC (r : Nat) : Nat := Nat.land r (nat_lit 15)

@[expose] noncomputable def opA (r : Nat) : Nat := fld(r, nat_lit 4, nat_lit 65535)

@[expose] noncomputable def opB (r : Nat) : Nat := fld(r, nat_lit 20, nat_lit 65535)

@[expose] noncomputable def opK (r : Nat) : Nat := fld(r, nat_lit 36, nat_lit 65535)

@[expose] noncomputable def getR (d : Nat) (R : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) R i

@[expose] noncomputable def setR (R : List Nat) (k v : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x xs ih k => Nat.rec (motive := fun _ => List Nat) (List.cons v xs)
      (fun j _ => List.cons x (ih j)) k) R k

@[expose] noncomputable def repR (c d : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun _ ih => List.cons d ih) c

@[expose] noncomputable def initR (x y c idn : Nat) : List Nat := x :: y :: repR c idn

@[expose] noncomputable def runK (n w m nw idn nr : Nat) (H prog : List Nat) (K : List Nat → Bool)
    (R : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) K
    (fun r _ ih R =>
      strictB (getR idn R (opA r)) (fun x =>
      strictB (opK r) (fun k =>
      bAnd(Nat.blt k nr,
      strictB (opC r) (fun c =>
      bIf(Nat.beq c (nat_lit 0),
        strictB (getR idn R (opB r)) (fun y => strictB (pcomp n w m x y) (fun v => ih (setR R k v))),
      bIf(Nat.beq c (nat_lit 1),
        strictB (MOC.powK n w m idn x (opB r)) (fun v => ih (setR R k v)),
      bIf(Nat.beq c (nat_lit 2),
        strictB (getR (nat_lit 0) H (opB r)) (fun v => bAnd(permOK n w m nw x v, ih (setR R k v))),
        false))))))))
    prog R

@[expose] noncomputable def neAll (n w m f e : Nat) (c acc : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih acc => bAnd(bIf(Nat.beq f acc, false, true), strictB (pcomp n w m e acc) ih)) c acc

structure CGK where
  p : Nat
  nx1 : Nat
  prog1 : List Nat
  is1 : Nat
  is2 : Nat
  ke : Nat
  kf : Nat
  nx2 : Nat
  prog2 : List Nat
  ra : Nat
  rb : Nat
  hints : List Nat

@[expose] noncomputable def finK (n w m nw idn A B : Nat) (D : CGK) (R1 : List Nat) : Bool :=
  strictB (getR idn R1 D.is1) (fun s1 => strictB (getR idn R1 D.is2) (fun s2 =>
  strictB (MOC.powK n w m idn s1 D.ke) (fun e => strictB (MOC.powK n w m idn s2 D.kf) (fun f =>
  bAnd(Nat.beq (MOC.powK n w m idn e D.p) idn,
  bAnd(Nat.beq (MOC.powK n w m idn f D.p) idn,
  bAnd(Nat.beq (pcomp n w m e f) (pcomp n w m f e),
  bAnd(bIf(Nat.beq e idn, false, true),
  bAnd(neAll n w m f e D.p idn,
  runK n w m nw idn (Nat.add D.nx2 (nat_lit 2)) D.hints D.prog2
    (fun R2 => bAnd(Nat.beq (getR idn R2 D.ra) A, Nat.beq (getR idn R2 D.rb) B))
    (initR s1 s2 D.nx2 idn))))))))))

@[expose] noncomputable def cgK (n w A B : Nat) (D : CGK) : Bool :=
  strictB (mask w) (fun m => strictB (Nat.mul n w) (fun nw => strictB (pidn n w) (fun idn =>
  bAnd(szOK n w,
  bAnd(Nat.beq (Nat.shiftRight A nw) (nat_lit 0),
  bAnd(Nat.beq (Nat.shiftRight B nw) (nat_lit 0),
  runK n w m nw idn (Nat.add D.nx1 (nat_lit 2)) D.hints D.prog1 (finK n w m nw idn A B D)
    (initR A B D.nx1 idn)))))))

end CFSG.KC.CentGenK

end
