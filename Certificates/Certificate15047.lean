module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests
import Certificates.Kernel.LocalComp.HeAutCheck

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15047 : CFSG.ComponentClassification.AS81.HeSylow.heAutSylowCheck = true :=
  KernelLC.HeAutCheck.heAutSylowCheck_true

end Certificates
