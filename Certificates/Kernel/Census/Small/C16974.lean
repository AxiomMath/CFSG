module

public import CFSG.GF2Type.Smith1979.GammaU.SingCountInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG.GF2Type.Smith1979.GammaU in
theorem check16974 : singCount () = true := by
  decide +kernel

end CertificateChecks.KernelCensus
