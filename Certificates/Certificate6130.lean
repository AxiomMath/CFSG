module

public import Certificates.Data.Seitz77Sec27SmallJ2
public meta import Certificates.Data.Seitz77Sec27SmallJ2
import Certificates.Kernel.Seitz77.J2U0K

public section

namespace Certificates

open CertificateChecks

theorem certificate6130 : Seitz77Sec27.j2U0Check = true := KernelSeitz77.J2U0K.j2U0Check_true

end Certificates
