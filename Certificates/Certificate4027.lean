module

public import CFSG.Sporadic.J4.QT2LocX0CheckInputs
import Certificates.Kernel.J4Q.C4027

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem certificate4027 : chkX0All = true := KernelJ4Q.c4027

end Certificates
