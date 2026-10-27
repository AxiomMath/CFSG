module

public import Certificates.Data.ChengHeldExcl1Facts
import Certificates.Kernel.ChengHeld.Excl1F

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ChengHeldData in
theorem certificate6140 : chExcl1OK = true := KernelChengHeld.chExcl1_true

end Certificates
