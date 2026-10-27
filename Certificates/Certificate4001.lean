module

public import CFSG.Sporadic.J4.QT2ARadNative
import Certificates.Kernel.J4Q.C4001

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2A in
theorem certificate4001 : (chkQconj5 = true)
    ∧ (chkQlet = true) := KernelJ4Q.c4001

end Certificates
