module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsTests
import Certificates.Kernel.LocalComp.HeModelCheck

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15084 : CFSG.ComponentClassification.AS81.HeTri.heModelCheck = true := KernelLC.HeModelCheck.heModelCheck_true

end Certificates
