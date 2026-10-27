module

public import Certificates.Data.ChengHeldPresProps
import Certificates.Kernel.ChengHeld.PropsF

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ChengHeldData in
theorem certificate6138 : chPropsOK = true := KernelChengHeld.P.chProps_true

end Certificates
