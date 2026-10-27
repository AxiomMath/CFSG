module

public import CFSG.Sporadic.Schreier.RuJ49Check
import Certificates.Kernel.SporSch.Ru.J49

public section

namespace Certificates

open CertificateChecks

theorem certificate7350 : CFSG.Sporadic.RuSchreier.J49.check () = true := KernelSporSch.RuJ49.c7350

end Certificates
