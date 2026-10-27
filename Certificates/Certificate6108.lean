module

public import CFSG.Sporadic.Recognition.LyonsLocalMcLInputs
import Certificates.Kernel.McLAS.F6108

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.McLAS in
theorem certificate6108 : pairCheck = true := KernelMcLAS.pairCheck_true

end Certificates
