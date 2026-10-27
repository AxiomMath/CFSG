module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNCenterInputs
import Certificates.Kernel.Sporadic.OddCore.HND0

public section

namespace CertificateChecks.Batch25670

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem hnFixCheck_0 : CFSG.EvenSporadicStandard.Solomon78.hnFixCheck = true := by
  unfold CFSG.EvenSporadicStandard.Solomon78.hnFixCheck
  rw [CertificateChecks.KernelSpor.HND.s4_eq]
  decide +kernel

end CertificateChecks.Batch25670

namespace Certificates

open CertificateChecks

theorem certificate25670 : CFSG.EvenSporadicStandard.Solomon78.hnFixCheck = true := CertificateChecks.Batch25670.hnFixCheck_0

end Certificates
