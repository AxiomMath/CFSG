module

public import CFSG.Sporadic.J4.QT2LocHNative
import Certificates.Kernel.J4Q.C4007

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem certificate4007 : (chkAll = true) := KernelJ4Q.c4007

end Certificates
