module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUU37
import Certificates.Kernel.TwoHSLe4.U37

public section

open CFSG.EvenSporadicStandard.TwoHS

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26823 : U37Facts :=
  u37Facts_of_check KernelTwoHSLe4.u3Check_true KernelTwoHSLe4.u7Check_true
    KernelTwoHSLe4.u7ex_true

end Certificates
