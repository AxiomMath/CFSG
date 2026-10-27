module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6SimpleWeylCheck

public section

namespace CertificateChecks.KernelDirect.C63001

open CFSG.HardMathSupport.Timmesfeld.Tables.T1b

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem e6SimpleCheck_eq_true : e6SimpleCheck () = true := by
  decide +kernel

end CertificateChecks.KernelDirect.C63001
