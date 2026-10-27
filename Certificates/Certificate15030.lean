module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
import Certificates.Kernel.CosetJ.SuzTab

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15030 : CFSG.Sporadic.Recognition.SuzMultiplier.suzTabCheck = true := KernelCosetJ.SuzTab.check

end Certificates
