module

public import Certificates.Data.J4M2.Orbit
import Certificates.Kernel.J4M2.C4200

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.J4M2 in
theorem certificate4200 : chkGens = true ∧ chkOrbit = true ∧ chkV0 = true ∧ chkC = true := KernelJ4M2.c4200

end Certificates
