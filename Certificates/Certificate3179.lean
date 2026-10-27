module

public import CFSG.Monster.B.GSide.BT2BridgeDataWalk

public section

open CFSG.Monster.B.GSide CertificateChecks.KernelMonB

namespace Certificates

set_option maxRecDepth 100000

theorem walkSteps_bridge :
    walkSteps CodeT (@bridgeWalk) bridgeSteps = some .nil := by
  rw [walkSteps_congr _ adjDec CodeT _ codeTDec]
  decide +kernel

open CFSG.Monster.B.GSide in
theorem certificate3179 : walkSteps CodeT bridgeWalk bridgeSteps = some .nil :=
  walkSteps_bridge

end Certificates
