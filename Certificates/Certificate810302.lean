module

public import Certificates.Kernel.Sporadic.SuzI301K.Check

public section

namespace Certificates

open CFSG.Sporadic.SuzI301 in
theorem certificate810302 : suzCheck () = true :=
  CertificateChecks.KernelSpor.SuzI301K.suzCheck_true

end Certificates

end
