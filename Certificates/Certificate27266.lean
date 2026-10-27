module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7L39Data
import Certificates.Kernel.HSStd.PumpU3Glue

public section

open CFSG.EvenSporadicStandard.HSStd.PumpTC7

namespace Certificates

open CertificateChecks

theorem u3OK_true : u3OK = true := KernelHSStd.PumpU3.u3OK_true

theorem certificate27266 : CFSG.EvenSporadicStandard.HSStd.PumpTC7.u3OK = true := u3OK_true

end Certificates
