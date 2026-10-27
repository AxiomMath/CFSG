module

public import Certificates.Data.Kernel.Co2Dc2.Data

public section

namespace CFSG.KD.Co2Dc2

open CFSG.KC.SLD2

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 (J.lc.getD l 0) p

@[expose] noncomputable def P (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 J.pi p

@[expose] noncomputable def Q (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 J.pii p

@[expose] def hw : List Nat :=
  [0, 0, 0, 0, 7, 7, 7, 7, 7, 7, 7, 7, 6, 7, 7, 7, 7, 7, 7, 7, 7, 6, 7, 6, 7, 7, 7, 6, 7, 7, 7, 0,
    1, 3, 2, 0, 0]

@[expose] noncomputable def C : Dc2Ctx where
  n := 2300
  L := L
  nl := 8
  ns := 5
  nf := 6
  Λ := J.Lam
  Δ := J.Delta
  k := 18
  N1 := 46575
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
  (List.range 2300).all fun p =>
    Nat.blt (P p) 2300 && Nat.blt (Q p) 2300 && Nat.beq (P (Q p)) p && Nat.beq (Q (P p)) p

@[expose] noncomputable def hwOK : Bool :=
  (List.range 2300).all fun p => Nat.beq (L 5 p) (CFSG.KC.E64F.wordF L hw p)

end CFSG.KD.Co2Dc2

end
