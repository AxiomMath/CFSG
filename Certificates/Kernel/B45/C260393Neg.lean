module

public import Certificates.Kernel.B45.C260393D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.B45.C260393Neg

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.LQT.SV CFSG.KC.B45P CFSG.KD.B45.C260393
  CertificateChecks.KernelSporSch.RuG

theorem word : (tGenK 4060 12 [A0, A1] [A0I, A1I] A0 A0I (SY.G.getD 0 0) (wsK.getD 4 [])).not =
    true := by quickRfl

theorem comm : (tGenK 4060 12 [A0, A1] [A0I, A1I] A1 A1I (SY.G.getD 4 0) (wsK.getD 4 [])).not =
    true := by quickRfl

theorem elt : (chunkSV 4060 12 256 7 SY.G.reverse SY.E SY.PT SY.LT SY.TB 1 1).not = true := by
  quickRfl

theorem pairs : (pairsSV 12 256 SY.E [0, 1, 2, 3] 4).not = true := by quickRfl

theorem sort : (sortAllSV 256 SY.E SY.SR SY.IS).not = true := by quickRfl

theorem bind : (bindSV SY.LabL SY.PT 256).not = true := by quickRfl

end CFSG.KD.B45.C260393Neg

end
