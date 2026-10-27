module

public import CFSG.Sporadic.Recognition.J4MultiplierInputs
import Certificates.Kernel.CosetJ.J4

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15042 : CFSG.Sporadic.Recognition.J4Multiplier.J4FoxCert := KernelCosetJ.J4.foxCert

end Certificates
