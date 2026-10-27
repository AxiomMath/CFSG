module

public import CFSG.Sporadic.J4.QT2LocFixNative
import Certificates.Kernel.J4Q.C4005

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem certificate4005 : (chkFix2B = true)
    ∧ (chkFix2A = true) := KernelJ4Q.c4005

end Certificates
