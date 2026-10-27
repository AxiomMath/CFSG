module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BabyMonster.PcFive
public import Certificates.Kernel.BabyMonster.PcFive.Data

public section

namespace CFSG.KC.BM.PcFiveD

open CFSG.KC.BM.PcFive

theorem t0 : chunkOK rep 152 0 c0 = true := by quickRfl
theorem t1 : chunkOK rep 152 1000 c1 = true := by quickRfl
theorem t2 : chunkOK rep 152 2000 c2 = true := by quickRfl
theorem t3 : chunkOK rep 152 3000 c3 = true := by quickRfl

end CFSG.KC.BM.PcFiveD

end
