
module


public import CFSG.Sporadic.Fi23.InvCertInputs
import Certificates.Kernel.Fi23S.Fact1014

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native in
theorem certificate1014 : invCertificate 3 = true := KernelFi23S.cover_ok

end Certificates
