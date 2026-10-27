module

public import CFSG.Sporadic.Schreier.LyCheckGLQ
import Certificates.Kernel.SporSch.Ly.GLQ2334
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native in
theorem certificate2334 : glqCertificate () = true := KernelSporSch.LyGQF.facts

end Certificates
