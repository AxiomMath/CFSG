module

public import CFSG.Sporadic.Fi23.S12CertInputs
import Certificates.Kernel.Fi23S.Fact10087

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23.Native in
theorem certificate10087 :
    s12Certificate = true := KernelFi23S.s12_ok

end Certificates
