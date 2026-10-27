module

public import Certificates.Data.ChengHeldPres
import Certificates.Kernel.ChengHeld.PresF

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ChengHeldData in
theorem certificate6137 : chPresOK = true := KernelChengHeld.chPres_true

end Certificates
