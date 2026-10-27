module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
import Certificates.Kernel.CosetJ.Rho0

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15031 : CFSG.Sporadic.Recognition.SuzMultiplier.suzRho0Check = true := KernelCosetJ.Rho0.check

end Certificates
