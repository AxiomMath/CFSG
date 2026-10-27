module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenData
import Certificates.Kernel.Co2Eleven.Glue7

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative in
theorem certificate16960 : co2SevenOK co2SevenData 7 56 = true := KernelCo2Eleven.seven_ok

end Certificates
