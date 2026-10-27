module

public import CFSG.Sporadic.Co2Schreier.IndexNineInputs
import Certificates.Kernel.Co2IndexNine.Words

public section

namespace Certificates

theorem certificate744102 : CFSG.Sporadic.Co2Schreier.co2IndexNineWordCheck () = true :=
  CertificateChecks.KernelCo2IndexNine.check

end Certificates
