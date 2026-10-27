module

public import CFSG.HardMathSupport.MathTwE6.M3BIrrCheck
import Certificates.Kernel.M3BIrr

public section

namespace Certificates

open CertificateChecks

theorem certificate136207 : CFSG.HardMathSupport.MathTwE6.M3BIrr.irrCheck () = true := KernelM3BIrr.irrCheck_true

end Certificates
