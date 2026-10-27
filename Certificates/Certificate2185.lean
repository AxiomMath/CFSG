module

public import CFSG.Sporadic.Schreier.LyCheckOrbit
import Certificates.Kernel.Ly3085.RootKey

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native in
theorem certificate2185 : bpRootChecks () = true := KernelLy.rootChecks

end Certificates
