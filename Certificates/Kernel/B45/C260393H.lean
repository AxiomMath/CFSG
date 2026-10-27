module

public import Certificates.Kernel.B45.C260393D
public import Certificates.Data.Kernel.LocalQT.Nats
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.B45.C260393

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.LQT.SV CFSG.KC.LQT.NP CFSG.KC.IntLines
  CFSG.KC.LQT.Cov

theorem strs : ([C0.chars, C1.chars, C2.chars, C3.chars, C4.chars, C5.chars, C6.chars].all
    fun l => (intsSK (tokK l)).isSome) = true := by quickRfl

theorem pP : natsOK CP.chars SY.ParL = true := by quickRfl
theorem pL : natsOK CL.chars SY.LabL = true := by quickRfl
theorem pT : natsOK CT.chars SY.TabL = true := by quickRfl
theorem bP : bindSV SY.ParL SY.PT 256 = true := by quickRfl
theorem bL : bindSV SY.LabL SY.LT 256 = true := by quickRfl
theorem bT : bindSV SY.TabL SY.TB (256 * 7) = true := by quickRfl
theorem hSY : headSV 4060 12 256 7 SY.G SY.GI = true := by quickRfl
theorem sSY : sortAllSV 256 SY.E SY.IS SY.SR = true := by quickRfl
theorem qSY : pairsSV 12 256 SY.E [0, 1, 2, 3] 5 = true := by quickRfl

end CFSG.KD.B45.C260393

end
