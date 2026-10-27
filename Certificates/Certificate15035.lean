module

public import CFSG.Sporadic.Recognition.SuzMultiplierIndex
import Certificates.Kernel.CosetJ.Suz2

public section

namespace Certificates

open CertificateChecks

theorem certificate15035 : CFSG.Sporadic.Recognition.SuzMultiplier.SuzCardP2 := KernelCosetJ.Suz2.card

end Certificates
