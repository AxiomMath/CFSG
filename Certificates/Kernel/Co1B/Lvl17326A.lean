module

public import Certificates.Kernel.Co1B.Data17326
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17326

open CFSG.KC.Co1BBoundP CFSG.KLie.CT

@[expose] noncomputable def ch17326pA (n : Nat) : Bool :=
  lvlChunkP 5 CertificateChecks.KernelCo1B.Bound17591.XB KC.T KC.CFs KC.NP
    CertificateChecks.KernelCo1B.CV.F KC.CNs n

theorem negChunk17326A : notB (lvlChunkP 5 CertificateChecks.KernelCo1B.Bound17591.XB KC.T KC.CFs
    KC.NP CertificateChecks.KernelCo1B.CV.F (KC.CNs.map fun l => l.map (· + 1)) 9) = true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17326

#kc_each CertificateChecks.KernelCo1B.Bound17326.ch17326pA 0 63

end
