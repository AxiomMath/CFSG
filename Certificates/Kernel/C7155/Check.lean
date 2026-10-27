module

public import Certificates.Data.Kernel.C7155.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.C7155

open CFSG.KC.C7155 CFSG.KC.Ord

theorem ch7155_buckets : bucketsOK bits11625 = true := by quickRfl

theorem ch7155_pt : ptOKL tC = true := by quickRfl

theorem ch7155_lev : levOKL tC = true := by quickRfl

end CFSG.KD.C7155

end
