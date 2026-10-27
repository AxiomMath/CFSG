module

public import CFSG.Sporadic.J4.QT2LocVLNative
import Certificates.Kernel.J4Q.C4011

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem certificate4011 : (chkVlAll = true) := KernelJ4Q.c4011

end Certificates
