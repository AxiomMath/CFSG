module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE7
import Certificates.Kernel.Direct.C13605

public section

namespace Certificates

open CertificateChecks

theorem certificate13605 : CFSG.HardMathSupport.Timmesfeld.Steinberg.e7ThreeCheck () = true :=
  KernelDirect.C13605.e7ThreeCheck_eq_true

end Certificates
