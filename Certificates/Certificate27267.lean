module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H39Data
import Certificates.Kernel.HSStd.PumpH39Glue

public section

open CFSG.EvenSporadicStandard.HSStd.PumpTC7

namespace Certificates

open CertificateChecks

theorem h39OK_true : h39OK = true := KernelHSStd.PumpH39.h39OK_true

theorem certificate27267 : CFSG.EvenSporadicStandard.HSStd.PumpTC7.h39OK = true := h39OK_true

end Certificates
