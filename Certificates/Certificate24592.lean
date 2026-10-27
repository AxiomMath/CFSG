module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J2ECheck
import Certificates.Kernel.J2Cover.E24592

public section

namespace Certificates

open CertificateChecks

theorem certificate24592 : CFSG.EvenSporadicStandard.Fin76b.J2.j2ECheck = true := KernelJ2Cover.c24592

end Certificates
