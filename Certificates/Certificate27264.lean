module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCatLie
import Certificates.Kernel.LieOrders.HS

public section

open CFSG.EvenSporadicStandard.HSStd.PumpHS

namespace Certificates

open CertificateChecks

theorem hsLieCheck_true : hsLieCheck = true := KernelLieOrders.hsLieCheck_true

theorem certificate27264 : CFSG.EvenSporadicStandard.HSStd.PumpHS.hsLieCheck = true := hsLieCheck_true

end Certificates
