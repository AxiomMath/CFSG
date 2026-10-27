
module


import Certificates.Kernel.Th.Dce
public import CFSG.Certificates.Kernel.Th.Soundness

public section

namespace Certificates

open CertificateChecks

theorem certificate9131 : Finite TauCeti.SporadicName.Th.Group ∧
    Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000 :=
  CFSG.KC.Th.Soundness.dce_sound KernelTh.dceData KernelTh.dce_ok

end Certificates
