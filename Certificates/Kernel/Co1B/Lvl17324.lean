module

public import Certificates.Kernel.Co1B.Data17324
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17324

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch17324p (n : Nat) : Bool :=
  lvlChunkP 5 CertificateChecks.KernelCo1B.Bound17591.XB KA.T KA.CFs KA.NP
    CertificateChecks.KernelCo1B.CV.F KA.CNs n

theorem negChunk17324Up : notB (lvlChunkP 5 CertificateChecks.KernelCo1B.Bound17591.XB KA.T KA.CFs
    KA.NP CertificateChecks.KernelCo1B.CV.F (KA.CNs.map fun l => l.map (· + 1)) 9) = true := by
  quickRfl

theorem negChunk17324Down : notB (lvlChunkP 5 CertificateChecks.KernelCo1B.Bound17591.XB KA.T
    KA.CFs KA.NP CertificateChecks.KernelCo1B.CV.F (KA.CNs.map fun l => l.map (· - 1)) 0) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17324

#kc_each CertificateChecks.KernelCo1B.Bound17324.ch17324p 0 54

end
