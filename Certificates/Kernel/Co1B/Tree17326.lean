module

public import Certificates.Kernel.Co1B.Data17326
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17326

open CFSG.KS.SporSch.M24 (gtPinK)
open CFSG.KLie.CT (notB)

@[expose] noncomputable def CM (l : Nat) : Nat := DC.M (Nat.add 90 l)

theorem kCT : (gtPinK CM 2 20000 CT.N CT.P CT.PAR CT.LAB CT.W CT.S && Nat.beq CT.N 15000) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17326

end
