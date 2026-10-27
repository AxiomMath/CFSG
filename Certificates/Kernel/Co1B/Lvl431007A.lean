module

public import Certificates.Kernel.Co1B.Data431007
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound431007

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch431007pA (n : Nat) : Bool :=
  lvlChunkP 25 CertificateChecks.KernelCo1B.Bound17591.XB KF.TA KF.CFsA KF.NPA
    CertificateChecks.KernelCo1B.CV.F KF.CNsA n

theorem negChunk431007A : notB (lvlChunkP 25 CertificateChecks.KernelCo1B.Bound17591.XB KF.TA
    KF.CFsA KF.NPA CertificateChecks.KernelCo1B.CV.F (KF.CNsA.map fun l => l.map (· + 1)) 9) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound431007

#kc_each CertificateChecks.KernelCo1B.Bound431007.ch431007pA 0 27

end
