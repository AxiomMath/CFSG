module

public import Certificates.Data.Kernel.B45Perm.Defs
public import Certificates.Data.SmithB45ExcHSData
public import Certificates.Kernel.LocalQT.SV.C4126T
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.B45.C260390

open CFSG.KC.Enum CFSG.KC.B45P CFSG.KC.PkPow CFSG.Quasithin.B45Exc.HS CFSG.KD.LQT.C4126

theorem hs0K : b45OrdK 3850 12 5 [HS.F 0, HS.F 1] [HSI 0, HSI 1] (HC.F 5) (HC.F 5) hsW0 = true := by
  quickRfl

theorem hs1K : b45CfgK 3850 12 5 [HS.F 0, HS.F 1] [HSI 0, HSI 1] (HC.F 12) (HC.F 12) hsW1g hsW1x
    hsW1y = true := by
  quickRfl

theorem hs3K : b45CfgK 3850 12 5 [HS.F 0, HS.F 1] [HSI 0, HSI 1] (HC.F 34) (HC.F 34) hsW3g hsW3x
    hsW3y = true := by
  quickRfl

theorem hsFix5K : Nat.beq (nfix 3850 12 (HC.F 5)) 170 = true := by quickRfl

theorem hsFix12K : Nat.beq (nfix 3850 12 (HC.F 12)) 30 = true := by quickRfl

theorem hsFix21K : Nat.beq (nfix 3850 12 (HC.F 21)) 350 = true := by quickRfl

theorem hsFix34K : Nat.beq (nfix 3850 12 (HC.F 34)) 46 = true := by quickRfl

end CFSG.KD.B45.C260390

end
