module

public import Certificates.Data.CFSGNative.Fi23.Centralizer
import Certificates.Kernel.Fi23C.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native in
theorem certificate1011 : CFSG.Sporadic.Fi23.Native.centCertificate 3 = true := KernelFi23C.cent_ok

end Certificates
