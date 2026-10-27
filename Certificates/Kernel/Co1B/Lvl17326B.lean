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

@[expose] noncomputable def ch17326pB (n : Nat) : Bool :=
  lvlChunkP 7 CertificateChecks.KernelCo1B.Bound17591.XB KC.T2 KC.CFs2 KC.NP2
    CertificateChecks.KernelCo1B.CV.F KC.CNs2 n

theorem negChunk17326B : notB (lvlChunkP 7 CertificateChecks.KernelCo1B.Bound17591.XB KC.T2
    KC.CFs2 KC.NP2 CertificateChecks.KernelCo1B.CV.F (KC.CNs2.map fun l => l.map (· + 1)) 0) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17326

#kc_each CertificateChecks.KernelCo1B.Bound17326.ch17326pB 0 36

end
