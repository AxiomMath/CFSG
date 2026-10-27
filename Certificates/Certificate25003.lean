module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowCheck
import Certificates.Kernel.EvenSporSuz.Bridge

public section

namespace CertificateChecks.Batch25003

theorem jCheck_0 : CFSG.EvenSporadicStandard.TwoSuz.jCheck = true := KernelSuz.jCheck_true

end CertificateChecks.Batch25003

namespace Certificates

open CertificateChecks

theorem certificate25003 : CFSG.EvenSporadicStandard.TwoSuz.jCheck = true := CertificateChecks.Batch25003.jCheck_0

end Certificates
