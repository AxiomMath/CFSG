module

public import Certificates.Kernel.Co1B.Data17620
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17620

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch17620q (n : Nat) : Bool :=
  lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KA.T ([] :: KA.CFt) KA.NP
    CertificateChecks.KernelCo1B.CV.F KA.CNs n

end CertificateChecks.KernelCo1B.Bound17620

#kc_each CertificateChecks.KernelCo1B.Bound17620.ch17620q 36 72

end
