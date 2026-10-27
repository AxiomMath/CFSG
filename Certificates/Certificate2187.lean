module

public import CFSG.Sporadic.Schreier.LyCheckR3E
import Certificates.Kernel.SporSch.Ly.R3E2187
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native in
theorem certificate2187 : r3eCertificate () = true := KernelSporSch.LyR3E.facts

end Certificates
