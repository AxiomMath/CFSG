module

public import Certificates.Kernel.Co1M.D10078
public import Certificates.Data.Kernel.Co1M.InvFam
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree

theorem k78_t11b : chunksK (actV RT78 [12, 13, 14, 15, 16]) 5 15259617 (recT t11bL78 6 40) 672 24 3 10
    64 0 11 = true := by quickRfl

theorem k78_t7b : chunksK (actV RT78 [23, 24, 25, 26, 27]) 5 10361096 (recT t7bL78 6 42) 2640 24 3 12
    64 0 42 = true := by quickRfl

theorem k78_t7c : chunksK (actV RT78 [28, 29, 30, 31, 32]) 5 459969 (recT t7cL78 6 32) 8 24 2 3
    64 0 1 = true := by quickRfl

theorem k78_t5b_0 : chunksK (actV RT78 [39, 40, 41, 42, 43]) 5 9326441 (recT t5bL78 6 43) 6144 24 3 13
    64 0 48 = true := by quickRfl

theorem k78_t5b_1 : chunksK (actV RT78 [39, 40, 41, 42, 43]) 5 9326441 (recT t5bL78 6 43) 6144 24 3 13
    64 48 48 = true := by quickRfl

theorem k78_t5c : chunksK (actV RT78 [44, 45, 46, 47, 48]) 5 5595851 (recT t5cL78 6 32) 6 24 2 3
    64 0 1 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
