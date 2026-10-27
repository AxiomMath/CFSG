module

public import Certificates.Data.CFSGNative.Fi23.Classes
import Certificates.Kernel.Fi23S.Fact1013

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native in
theorem certificate1013 : classesCertificate 3 = true := KernelFi23S.classes_ok

end Certificates
