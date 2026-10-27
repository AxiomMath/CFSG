module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4FusYTests
import Certificates.Kernel.LocalComp.FusYCheck

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15056 : CFSG.ComponentClassification.AS81.FusY.fusYCheck = true := KernelLC.FusY.fusYCheck_true

end Certificates
