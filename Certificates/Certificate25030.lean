module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterCheck
import Certificates.Kernel.EvenSporSuz.Outer25030F

public section

namespace CertificateChecks.Batch25030

theorem outerCheck_0 : CFSG.EvenSporadicStandard.TwoSuz.outerCheck = true :=
  KernelSpor.S26990.check25030

end CertificateChecks.Batch25030

namespace Certificates

open CertificateChecks

theorem certificate25030 : CFSG.EvenSporadicStandard.TwoSuz.outerCheck = true := CertificateChecks.Batch25030.outerCheck_0

end Certificates
