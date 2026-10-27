module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyThrData
import Certificates.Kernel.HS100.FyThrGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26792 : fyThrOK = true := KernelHS100.fyThr

end Certificates
