module

public import Certificates.Kernel.Co1B.Data17620
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17620

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch17620p (n : Nat) : Bool :=
  lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KA.T ([] :: KA.CFt) KA.NP
    CertificateChecks.KernelCo1B.CV.F KA.CNs n

theorem negChunk17620Up : notB (lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KA.T
    ([] :: KA.CFt) KA.NP CertificateChecks.KernelCo1B.CV.F (KA.CNs.map fun l => l.map (· + 1)) 10) =
    true := by
  quickRfl

theorem negChunk17620Down : notB (lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KA.T
    ([] :: KA.CFt) KA.NP CertificateChecks.KernelCo1B.CV.F (KA.CNs.map fun l => l.map (· - 1)) 0) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17620

#kc_each CertificateChecks.KernelCo1B.Bound17620.ch17620p 0 36

end
