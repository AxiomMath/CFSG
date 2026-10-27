module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BabyMonster.PcFive
public import Certificates.Kernel.BabyMonster.PcFive.Data

public section

namespace CFSG.KC.BM.PcFiveD

open CFSG.KC.BM.PcFive

theorem t12 : chunkOK rep 152 12000 c12 = true := by quickRfl
theorem t13 : chunkOK rep 152 13000 c13 = true := by quickRfl
theorem t14 : chunkOK rep 152 14000 c14 = true := by quickRfl
theorem t15 : chunkOK rep 152 15000 c15 = true := by quickRfl

end CFSG.KC.BM.PcFiveD

end
