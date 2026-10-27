module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE8

public section

namespace CertificateChecks.KernelDirect.C13691

open CFSG.HardMathSupport.Timmesfeld.Steinberg

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem e8ThreeOrbit_ok : orbitCheck3 .E8 e8ThreeReps e8ThreeOrbit = true := by
  decide +kernel

end CertificateChecks.KernelDirect.C13691
