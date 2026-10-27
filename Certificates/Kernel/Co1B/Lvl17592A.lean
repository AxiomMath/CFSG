module

public import Certificates.Kernel.Co1B.Data17592
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17592

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch17592p (n : Nat) : Bool :=
  lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KD.T KD.CFs KD.NP
    CertificateChecks.KernelCo1B.CV.F KD.CNs n

theorem negChunk17592Up : notB (lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KD.T KD.CFs
    KD.NP CertificateChecks.KernelCo1B.CV.F (KD.CNs.map fun l => l.map (· + 1)) 9) = true := by
  quickRfl

theorem negChunk17592Down : notB (lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KD.T
    KD.CFs KD.NP CertificateChecks.KernelCo1B.CV.F (KD.CNs.map fun l => l.map (· - 1)) 0) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17592

#kc_each CertificateChecks.KernelCo1B.Bound17592.ch17592p 0 36

end
