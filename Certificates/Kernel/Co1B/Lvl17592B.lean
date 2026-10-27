module

public import Certificates.Kernel.Co1B.Data17592
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17592

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch17592q (n : Nat) : Bool :=
  lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KD.T KD.CFs KD.NP
    CertificateChecks.KernelCo1B.CV.F KD.CNs n

end CertificateChecks.KernelCo1B.Bound17592

#kc_each CertificateChecks.KernelCo1B.Bound17592.ch17592q 36 72

end
