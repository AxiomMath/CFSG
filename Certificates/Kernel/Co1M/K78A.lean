module

public import Certificates.Kernel.Co1M.D10078
public import Certificates.Data.Kernel.Co1M.InvFam
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree

theorem k78_t11a_0 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 13392743 (recT t11aL78 6 46) 20736 24 4 15
    64 0 54 = true := by quickRfl

theorem k78_t11a_1 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 13392743 (recT t11aL78 6 46) 20736 24 4 15
    64 54 54 = true := by quickRfl

theorem k78_t11a_2 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 13392743 (recT t11aL78 6 46) 20736 24 4 15
    64 108 54 = true := by quickRfl

theorem k78_t11a_3 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 13392743 (recT t11aL78 6 46) 20736 24 4 15
    64 162 54 = true := by quickRfl

theorem k78_t11a_4 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 13392743 (recT t11aL78 6 46) 20736 24 4 15
    64 216 54 = true := by quickRfl

theorem k78_t11a_5 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 13392743 (recT t11aL78 6 46) 20736 24 4 15
    64 270 54 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
