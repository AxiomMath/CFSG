module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE7

public section

namespace CertificateChecks.KernelDirect.C13605

open CFSG.HardMathSupport.Timmesfeld.Steinberg

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem e7ThreeCheck_eq_true : e7ThreeCheck () = true := by
  decide +kernel

end CertificateChecks.KernelDirect.C13605
