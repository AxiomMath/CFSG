module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYM12Data
import Certificates.Kernel.HSStd.M12FyGlue

public section

open CFSG.EvenSporadicStandard.HSStd.FiveY

namespace Certificates

open CertificateChecks

theorem m12OK_true : m12OK = true := KernelHSStd.M12Fy.m12OK_true

theorem certificate27262 : CFSG.EvenSporadicStandard.HSStd.FiveY.m12OK = true := m12OK_true

end Certificates
