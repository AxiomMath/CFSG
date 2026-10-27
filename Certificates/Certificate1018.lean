
module


public import CFSG.Sporadic.Fi24.ExtCertInputs
import Certificates.Kernel.Sporadic.Fi24Ext.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native in
theorem certificate1018 : extChecks () = true := KernelFi24Ext.extChecks_true

end Certificates

end
