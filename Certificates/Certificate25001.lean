module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.CoverCheck
import Certificates.Kernel.EvenSporSuz.CoverGlue

public section

namespace CertificateChecks.Batch25001

theorem coverCheck_0 : CFSG.EvenSporadicStandard.TwoSuz.coverCheck = true := KernelSuz.coverCheck_true

end CertificateChecks.Batch25001

namespace Certificates

open CertificateChecks

theorem certificate25001 : CFSG.EvenSporadicStandard.TwoSuz.coverCheck = true := CertificateChecks.Batch25001.coverCheck_0

end Certificates
