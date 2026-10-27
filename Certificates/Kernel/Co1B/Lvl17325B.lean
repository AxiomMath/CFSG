module

public import Certificates.Kernel.Co1B.Data17325
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17325

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch17325pB (n : Nat) : Bool :=
  lvlChunkP 5 CertificateChecks.KernelCo1B.Bound17591.XB KB.T2 KB.CFs2 KB.NP2
    CertificateChecks.KernelCo1B.CV.F KB.CNs2 n

theorem negChunk17325B : notB (lvlChunkP 5 CertificateChecks.KernelCo1B.Bound17591.XB KB.T2
    KB.CFs2 KB.NP2 CertificateChecks.KernelCo1B.CV.F (KB.CNs2.map fun l => l.map (· + 1)) 0) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17325

#kc_each CertificateChecks.KernelCo1B.Bound17325.ch17325pB 0 54

end
