module

import Certificates.Kernel.J4Q.C4116
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.J4.QT2LocX0Native

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 in
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 in
theorem certificate4116 : (∀ c < 2048, wfRows (etaE c) = true) := KernelJ4Q.c4116

end Certificates
