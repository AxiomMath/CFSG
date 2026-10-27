module

public import Certificates.Data.ChengHeldSec2Facts
import Certificates.Kernel.ChengHeld.Sec2F

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ChengHeldData in
theorem certificate6139 : chSec2OK = true := KernelChengHeld.S2.chSec2_true

end Certificates
