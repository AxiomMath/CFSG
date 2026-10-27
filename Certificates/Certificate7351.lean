module

public import CFSG.Sporadic.Schreier.RuJ49Sl2
import Certificates.Kernel.SporSch.Ru.J49

public section

namespace Certificates

open CertificateChecks

theorem certificate7351 : CFSG.Sporadic.RuSchreier.J49.Sl2.check () = true := KernelSporSch.RuJ49.c7351

end Certificates
