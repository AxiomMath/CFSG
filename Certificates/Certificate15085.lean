module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlueTests
import Certificates.Kernel.LocalComp.HeGlueCheck

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15085 : CFSG.ComponentClassification.AS81.HeTri.heGlueCheck = true := KernelLC.HeGlue.heGlueCheck_true

end Certificates
