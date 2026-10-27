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

@[expose] noncomputable def ch17329pB (n : Nat) : Bool :=
  lvlChunkP 243 CertificateChecks.KernelCo1B.Bound17591.XB KF.T2 KF.CFs2 KF.NP2
    CertificateChecks.KernelCo1B.CV.F KF.CNs2 n

theorem negChunk17329B : notB (lvlChunkP 243 CertificateChecks.KernelCo1B.Bound17591.XB KF.T2
    KF.CFs2 KF.NP2 CertificateChecks.KernelCo1B.CV.F (KF.CNs2.map fun l => l.map (· + 1)) 9) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17329

#kc_each CertificateChecks.KernelCo1B.Bound17329.ch17329pB 0 54

end
