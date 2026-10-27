module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE8

public section

namespace CertificateChecks.KernelDirect.C13691

open CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.Blueprint.Chevalley

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem e8ThreeStab2_ok : (e8ThreeStab2.check e8Certificate &&
    decide ((e8ThreeStab2.passing e8Certificate).length ≤ 1)) = true := by
  decide +kernel

end CertificateChecks.KernelDirect.C13691
