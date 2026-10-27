module

public import CFSG.Sporadic.Schreier.LyCheckSeven
import Certificates.Kernel.SporSch.Ly.Seven2189

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native in
theorem certificate2189 : sevenCertificate () = true := KernelSporSch.LySvF.facts

end Certificates
