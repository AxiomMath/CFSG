module

public import CFSG.Sporadic.Schreier.LyCheckCover
import Certificates.Kernel.SporSch.Ly.Cover2184

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native in
theorem certificate2184 : coverCertificate () = true := KernelSporSch.LyCvF.facts

end Certificates
