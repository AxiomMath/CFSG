module

public import Certificates.Data.Kernel.Fi22Dc2.Data

public section

namespace CFSG.KD.Fi22Dc2

open CFSG.KC.SLD2

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 (J.lc.getD l 0) p

@[expose] noncomputable def P (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 J.pi p

@[expose] noncomputable def Q (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 J.pii p

@[expose] def hw : List Nat := [6, 0, 5, 0, 5, 3, 6]

@[expose] def tw (j : Nat) : List Nat :=
  [[3, 0, 3, 1, 2, 1, 3, 3, 2, 0], [0], [1], [2], [3, 2, 3, 0, 1, 2, 3, 1, 3, 1], [3],
    [0, 3, 2, 0, 2, 3, 2, 2, 0], [2, 2, 2, 1, 2, 1], [3, 3, 3, 0, 3, 2, 0, 2]].getD j []

@[expose] noncomputable def C : Dc2Ctx where
  n := 3510
  L := L
  nl := 7
  ns := 4
  nf := 5
  Λ := J.Lam
  Δ := J.Delta
  k := 17
  N1 := 142155
  N2 := 3465

@[expose] noncomputable def D : Dc2Data where
  sep := J.sep
  pw := J.pw
  bo := J.bo
  R1 := J.R1
  fB := J.fB
  fC := J.fC
  fw := J.fw
  fpc := J.fpc
  fpar := J.fpar
  fvia := J.fvia
  ford := J.ford
  R2 := J.R2
  gw := J.gw
  gd := J.gd
  roots := J.roots

@[expose] noncomputable def permOK : Bool :=
  (List.range 3510).all fun p =>
    Nat.blt (P p) 3510 && Nat.blt (Q p) 3510 && Nat.beq (P (Q p)) p && Nat.beq (Q (P p)) p

@[expose] noncomputable def hwOK : Bool :=
  (List.range 3510).all fun p => Nat.beq (L 4 p) (CFSG.KC.E64F.wordF L hw p)

end CFSG.KD.Fi22Dc2

end
