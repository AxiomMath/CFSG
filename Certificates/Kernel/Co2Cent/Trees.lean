module

public import Certificates.Kernel.Co2Cent.Data
public import Certificates.Data.Kernel.OrbRow.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow

theorem ch17351_tA : allN 10 (levelK 2300 12 4095 SA 16 BA KA MA DA RA) = true := by quickRfl

theorem ch17351_tB : allN 7 (levelK 2300 12 4095 SB 17 BB KB MB DB RB) = true := by quickRfl

theorem ch17351_tL : allN 3 (levelK 2300 12 4095 SL 6 BL KL ML DL RL) = true := by quickRfl

theorem ch17351_fA : allN 10 (fun i => fixLvK 12 4095 SA 16 (getS MA i) BA i) = true := by
  quickRfl

theorem ch17351_fB : allN 7 (fun i => fixLvK 12 4095 SB 17 (getS MB i) BB i) = true := by
  quickRfl

theorem ch17351_fL : allN 3 (fun i => fixLvK 12 4095 SL 6 (getS ML i) BL i) = true := by
  quickRfl

end CFSG.KD.Co2Cent

end
