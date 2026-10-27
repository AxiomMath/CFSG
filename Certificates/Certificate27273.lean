module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
import Certificates.Kernel.U43Coset8.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd.U43 in
theorem certificate27273 : cosetCheck8 = true :=
  KernelU43Coset8.cosetCheck8_true

end Certificates
