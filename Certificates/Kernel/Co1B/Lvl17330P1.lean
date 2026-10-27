module

public import Certificates.Kernel.Co1B.Data17330P
public import Certificates.Kernel.Co1B.Data17330
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17330

open CFSG.KC.Co1BBoundP

@[expose] noncomputable def ch17330pA (n : Nat) : Bool :=
  lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB K.T KP.CFs KP.NP
    CertificateChecks.KernelCo1B.CV.F KP.CNs n

end CertificateChecks.KernelCo1B.Bound17330

#kc_each CertificateChecks.KernelCo1B.Bound17330.ch17330pA 0 126

end
