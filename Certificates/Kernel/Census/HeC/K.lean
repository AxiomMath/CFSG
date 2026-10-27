module

public import Certificates.Kernel.Census.HeC.Data
public import Certificates.Kernel.SporSch.HeT.Tab
public import Certificates.Kernel.LocalComp.HeFixData

public section

namespace CertificateChecks.KernelCensus.HeCj

open CFSG.KS CFSG.KC.Enum

@[expose] noncomputable def uP (x : Nat) : Nat := pg 14 (mask 14) CertificateChecks.KernelLC.HeFix.PU x

@[expose] noncomputable def nv (F : Nat) : Bool :=
  CFSG.KS.SporSch.nfValidK 5 CertificateChecks.KernelSpor.HeC.LR F

@[expose] def bsH : List Nat := [0, 1, 2, 3, 4]

end CertificateChecks.KernelCensus.HeCj

end
