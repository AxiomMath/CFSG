module

public import CFSG.Sporadic.Recognition.LyonsAS44McLInputs
import Certificates.Kernel.McLAS.F6109

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.McLAS in
theorem certificate6109 : nrmCheck = true := KernelMcLAS.nrmCheck_true

end Certificates
