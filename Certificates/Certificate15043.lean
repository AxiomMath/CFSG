module

public import CFSG.Sporadic.Recognition.J4MultiplierInputs
import Certificates.Kernel.CosetJ.J4

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15043 : CFSG.Sporadic.Recognition.J4Multiplier.J4FormCert := KernelCosetJ.J4.formCert

end Certificates
