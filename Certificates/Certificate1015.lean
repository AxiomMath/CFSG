module

public import Certificates.Data.CFSGNative.Fi23.Tr
import Certificates.Kernel.Fi23T.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native in
theorem certificate1015 : trCertificate 3 = true := KernelFi23T.tr_ok

end Certificates
