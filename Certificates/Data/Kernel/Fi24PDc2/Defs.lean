module

public import Certificates.Data.Kernel.Fi24PDc2.Data

public section

namespace CFSG.KD.Fi24PDc2

open CFSG.KC.SLD2 CFSG.KC.E64F

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 9 (LT.lc.getD l 0) p

@[expose] def Λ : List Nat :=
  [49, 109, 147, 150, 199, 203, 215, 220, 238, 239, 243, 267, 287, 301, 304, 347, 357, 372]

@[expose] def Δ : List Nat := [108773, 114079]

@[expose] noncomputable def C : Dc2Ctx := ⟨378, L, 8, 4, 6, Λ, Δ, 8, 567, 135⟩

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

@[expose] noncomputable def wOK (l : Nat) (w : List Nat) : Bool :=
  (List.range 378).all fun p => Nat.beq (L l p) (wordF L w p)

@[expose] noncomputable def shapeOK : Bool :=
  Nat.beq LT.hw.length 2 && LT.hw.all (fun w => w.all fun l => Nat.beq l 6 || Nat.beq l 7) &&
    Nat.beq LT.sgw.length 4 && LT.sgw.all (fun w => w.all fun l => Nat.beq l 4 || Nat.beq l 5)

@[expose] noncomputable def letOK : Bool :=
  wOK 4 (LT.hw.getD 0 []) && wOK 5 (LT.hw.getD 1 []) && wOK 0 (LT.sgw.getD 0 []) &&
    wOK 1 (LT.sgw.getD 1 []) && wOK 2 (LT.sgw.getD 2 []) && wOK 3 (LT.sgw.getD 3 [])

@[expose] noncomputable def sbOK : Bool :=
  CFSG.KC.SLDc.omC (fun l x => x.map fun p => bif Nat.blt p 378 then L l p else 0)
    [0, 1, 2, 5] 4 SB.B SB.C SB.rows SB.par SB.via SB.ord

end CFSG.KD.Fi24PDc2

end
