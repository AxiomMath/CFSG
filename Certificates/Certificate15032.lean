module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
import Certificates.Kernel.CosetJ.RhoJ2

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15032 : CFSG.Sporadic.Recognition.SuzMultiplier.suzRhoJ2Check = true := KernelCosetJ.RhoJ2.check

end Certificates
