module

public import Certificates.Data.Kernel.F2Set24Block
public import Certificates.Kernel.Co1KOrb.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pump

open CFSG.KC.F2Set24 CFSG.KD.Co1KOrb

@[expose] noncomputable def ch36909WB : List Nat :=
  [9676673, 4819714, 275588, 5088200, 4823440, 14928096]

@[expose] noncomputable def ch36909gray : List Nat :=
  [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5,
   0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]

theorem ch36909b : blockOK cY cT opsY opsT 2 98280 28 ch36909WB ch36909gray = true := by quickRfl

end CertificateChecks.KernelCo1Pump

end
