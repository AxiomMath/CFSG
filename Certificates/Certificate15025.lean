module

public import CFSG.Sporadic.Recognition.RuMultiplierInputs
import Certificates.Kernel.CosetJ.RhoRu

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15025 : CFSG.Sporadic.Recognition.RuMultiplier.ruRhoCheck = true := KernelCosetJ.RhoRu.check

end Certificates
