module

public import Certificates.Data.HSThreeKD
import Certificates.Kernel.HS100.KDGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate10139 : CFSG.LocalAnalysis.GLTheoremA.KD264HS.hsThreeOK () = true := KernelHS100.hsThreeKD

end Certificates
