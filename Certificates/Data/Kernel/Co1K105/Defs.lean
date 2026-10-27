module

public import Certificates.Data.Kernel.Co1K105.Data
public import Certificates.Data.Kernel.Co1K105.Letters

public section

namespace CFSG.KD.Co1K105

open CFSG.KC.SLD2

@[expose] noncomputable def C : Dc2Ctx where
  n := 512
  L := L
  nl := 17
  ns := 15
  nf := 16
  Λ := J.Lam
  Δ := J.Delta
  k := 20
  N1 := 135
  N2 := 315

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

end CFSG.KD.Co1K105

end
