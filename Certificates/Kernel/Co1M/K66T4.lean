module

public import Certificates.Kernel.Co1M.D10066
public import Certificates.Data.Kernel.Co1M.InvFam
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree

@[expose] noncomputable def t40F66 (q : Nat) : Bool :=
  chunksK (actV GT466 [0, 1]) 2 2 (recT t40L66 6 46) 48576 24 5 16 64 (Nat.mul q 100) 100

@[expose] noncomputable def t41F66 (q : Nat) : Bool :=
  chunksK (actV GT466 [0, 1]) 2 3 (recT t41L66 6 46) 49152 24 5 16 64 (Nat.mul q 100) 100

@[expose] noncomputable def t42F66 (q : Nat) : Bool :=
  chunksK (actV GT466 [0, 1]) 2 1336 (recT t42L66 6 40) 552 24 5 10 64 (Nat.mul q 100) 100

end CertificateChecks.KernelCo1M

#kc_slices CertificateChecks.KernelCo1M.T40x66 CertificateChecks.KernelCo1M.t40F66 8
#kc_slices CertificateChecks.KernelCo1M.T41x66 CertificateChecks.KernelCo1M.t41F66 8
#kc_slices CertificateChecks.KernelCo1M.T42x66 CertificateChecks.KernelCo1M.t42F66 1

end
