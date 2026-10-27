module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BabyMonster.PcFive
public import Certificates.Kernel.BabyMonster.PcFive.Data

public section

namespace CFSG.KC.BM.PcFiveD

open CFSG.KC.BM.PcFive

theorem t8 : chunkOK rep 152 8000 c8 = true := by quickRfl
theorem t9 : chunkOK rep 152 9000 c9 = true := by quickRfl
theorem t10 : chunkOK rep 152 10000 c10 = true := by quickRfl
theorem t11 : chunkOK rep 152 11000 c11 = true := by quickRfl

end CFSG.KC.BM.PcFiveD

end
