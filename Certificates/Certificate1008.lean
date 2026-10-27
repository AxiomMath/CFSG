module

public import Certificates.Data.CFSGNative.Fi22.LH
import Certificates.Kernel.Fi22LH.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native in
theorem certificate1008 : lhCertificate () = true := KernelFi22LH.lh_certificate

end Certificates
