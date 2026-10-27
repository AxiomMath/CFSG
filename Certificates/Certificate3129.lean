module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.OddSquareCertInputs
import Certificates.Kernel.TwoE6.OddSquare
import Certificates.Data.Kernel.CTIBqBind
import Certificates.Kernel.TwoE6.CTIBqData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.TwoE6 in
theorem certificate3129 : (frameCodesOK = true)
    ∧ (oddWitOK 1 6 wordY2a 8 3 wordY2b 4 3 37440 4112 = true)
    ∧ (oddWitOK 1 7 wordCY2a 4 3 wordCY2b 4 3 2096 4112 = true)
    ∧ (oddWitOK 32 7 wordY3a 1 3 wordY3b 2 3 102610 16 = true) := KernelTwoE6.cert3129

end Certificates
