module

public import Certificates.Data.Kernel.BabyMonster.PcFive
import Certificates.Kernel.BabyMonster.PcFive.Census

public section

namespace Certificates

open CertificateChecks

theorem certificate13624 : CFSG.KC.BM.PcFive.CensusFact ∧ CFSG.KC.BM.PcFive.phiOK () = true :=
  ⟨KernelBM.PcFive.censusFact, KernelBM.PcFive.phiOK_true⟩

end Certificates
