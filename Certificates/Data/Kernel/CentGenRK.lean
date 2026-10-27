module

public import Certificates.Data.Kernel.CentGenK

public section

namespace CFSG.KC.CentGenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

structure CGRK where
  p : Nat
  nx1 : Nat
  prog1 : List Nat
  ie : Nat
  jf : Nat
  is1 : Nat
  is2 : Nat
  nx2 : Nat
  prog2 : List Nat
  ra : Nat
  rb : Nat
  hints : List Nat

@[expose] noncomputable def finRK (n w m nw idn A B : Nat) (D : CGRK) (R1 : List Nat) : Bool :=
  strictB (getR idn R1 D.is1) (fun s1 => strictB (getR idn R1 D.is2) (fun s2 =>
  strictB (getR idn R1 D.ie) (fun e => strictB (getR idn R1 D.jf) (fun f =>
  bAnd(Nat.beq (MOC.powK n w m idn e D.p) idn,
  bAnd(Nat.beq (MOC.powK n w m idn f D.p) idn,
  bAnd(Nat.beq (pcomp n w m e f) (pcomp n w m f e),
  bAnd(bIf(Nat.beq e idn, false, true),
  bAnd(neAll n w m f e D.p idn,
  bAnd(Nat.beq (pcomp n w m s1 e) (pcomp n w m e s1),
  bAnd(Nat.beq (pcomp n w m s2 f) (pcomp n w m f s2),
  runK n w m nw idn (Nat.add D.nx2 (nat_lit 2)) D.hints D.prog2
    (fun R2 => bAnd(Nat.beq (getR idn R2 D.ra) A, Nat.beq (getR idn R2 D.rb) B))
    (initR s1 s2 D.nx2 idn))))))))))))

@[expose] noncomputable def cgRK (n w A B : Nat) (D : CGRK) : Bool :=
  strictB (mask w) (fun m => strictB (Nat.mul n w) (fun nw => strictB (pidn n w) (fun idn =>
  bAnd(szOK n w,
  bAnd(Nat.beq (Nat.shiftRight A nw) (nat_lit 0),
  bAnd(Nat.beq (Nat.shiftRight B nw) (nat_lit 0),
  runK n w m nw idn (Nat.add D.nx1 (nat_lit 2)) D.hints D.prog1 (finRK n w m nw idn A B D)
    (initR A B D.nx1 idn)))))))

end CFSG.KC.CentGenK

end
