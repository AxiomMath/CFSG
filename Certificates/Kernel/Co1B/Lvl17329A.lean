module

public import Certificates.Kernel.Co1B.Data17329
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17329

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch17329pA (n : Nat) : Bool :=
  lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KF.T CFs1 KF.NP
    CertificateChecks.KernelCo1B.CV.F KF.CNs n

theorem negChunk17329A : notB (lvlChunkP 3 CertificateChecks.KernelCo1B.Bound17591.XB KF.T
    CFs1 KF.NP CertificateChecks.KernelCo1B.CV.F (KF.CNs.map fun l => l.map (· + 1)) 54) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17329

#kc_each CertificateChecks.KernelCo1B.Bound17329.ch17329pA 54 135

end
