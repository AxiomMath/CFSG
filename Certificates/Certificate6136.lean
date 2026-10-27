module

public import Certificates.Data.ChengHeldCover
import Certificates.Kernel.L34W.ChCoverGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ChengHeldData in
theorem certificate6136 : chCoverOK = true := KernelL34W.chCover_true

end Certificates
