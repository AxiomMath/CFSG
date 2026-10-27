module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BabyMonster.PcFive
public import Certificates.Kernel.BabyMonster.PcFive.Data

public section

namespace CFSG.KC.BM.PcFiveD

open CFSG.KC.BM.PcFive

theorem t4 : chunkOK rep 152 4000 c4 = true := by quickRfl
theorem t5 : chunkOK rep 152 5000 c5 = true := by quickRfl
theorem t6 : chunkOK rep 152 6000 c6 = true := by quickRfl
theorem t7 : chunkOK rep 152 7000 c7 = true := by quickRfl

end CFSG.KC.BM.PcFiveD

end
