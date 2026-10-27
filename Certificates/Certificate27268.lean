module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H43Data
import Certificates.Kernel.HSStd.PumpH43Glue

public section

open CFSG.EvenSporadicStandard.HSStd.PumpTC7

namespace Certificates

open CertificateChecks

theorem h43OK_true : h43OK = true := KernelHSStd.PumpH43.h43OK_true

theorem certificate27268 : CFSG.EvenSporadicStandard.HSStd.PumpTC7.h43OK = true := h43OK_true

end Certificates
