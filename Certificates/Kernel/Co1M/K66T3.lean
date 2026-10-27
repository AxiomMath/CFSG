module

public import Certificates.Kernel.Co1M.D10066
public import Certificates.Data.Kernel.Co1M.InvFam
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree

@[expose] noncomputable def t30F66 (q : Nat) : Bool :=
  chunksK (actV GT366 [0, 1]) 2 2 (recT t30L66 6 40) 552 24 5 10 64 (Nat.mul q 100) 100

@[expose] noncomputable def t31F66 (q : Nat) : Bool :=
  chunksK (actV GT366 [0, 1]) 2 3 (recT t31L66 6 47) 37950 24 6 16 64 (Nat.mul q 100) 100

@[expose] noncomputable def t32F66 (q : Nat) : Bool :=
  chunksK (actV GT366 [0, 1]) 2 4 (recT t32L66 6 47) 48600 24 6 16 64 (Nat.mul q 100) 100

@[expose] noncomputable def t33F66 (q : Nat) : Bool :=
  chunksK (actV GT366 [0, 1]) 2 5 (recT t33L66 6 45) 11178 24 6 14 64 (Nat.mul q 100) 100

end CertificateChecks.KernelCo1M

#kc_slices CertificateChecks.KernelCo1M.T30x66 CertificateChecks.KernelCo1M.t30F66 1
#kc_slices CertificateChecks.KernelCo1M.T31x66 CertificateChecks.KernelCo1M.t31F66 6
#kc_slices CertificateChecks.KernelCo1M.T32x66 CertificateChecks.KernelCo1M.t32F66 8
#kc_slices CertificateChecks.KernelCo1M.T33x66 CertificateChecks.KernelCo1M.t33F66 2

end
