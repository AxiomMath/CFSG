module

public import CFSG.Sporadic.Schreier.LyCheckSylow
import Certificates.Kernel.SporSch.Ly.Syl2190
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native in
theorem certificate2190 : sylowCertificate () = true := KernelSporSch.LySyF.facts

end Certificates
