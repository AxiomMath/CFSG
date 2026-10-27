module

public import Certificates.Data.GrSLitL34Sec4OutCovCheck
import Certificates.Kernel.L34W.OutCovGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.GrS4.OutCov in
theorem certificate22971 : outCovOK = true := KernelL34W.outCovOK_true

end Certificates
