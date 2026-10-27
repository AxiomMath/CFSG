module

public import CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenInputs
import Certificates.Kernel.Co2Eleven.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenNative in
theorem certificate17707 : co2ElevenCheck () = true := KernelCo2Eleven.eleven_ok

end Certificates
