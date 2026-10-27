module

public import Certificates.Kernel.Co1M.D10078
public import Certificates.Data.Kernel.Co1M.InvFam
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree

theorem k78_t5a_0 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 1095512 (recT t5aL78 6 46) 24948 24 4 15
    64 0 65 = true := by quickRfl

theorem k78_t5a_1 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 1095512 (recT t5aL78 6 46) 24948 24 4 15
    64 65 65 = true := by quickRfl

theorem k78_t5a_2 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 1095512 (recT t5aL78 6 46) 24948 24 4 15
    64 130 65 = true := by quickRfl

theorem k78_t5a_3 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 1095512 (recT t5aL78 6 46) 24948 24 4 15
    64 195 65 = true := by quickRfl

theorem k78_t5a_4 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 1095512 (recT t5aL78 6 46) 24948 24 4 15
    64 260 65 = true := by quickRfl

theorem k78_t5a_5 : chunksK (actV RT78 [7, 8, 9, 10, 11]) 5 1095512 (recT t5aL78 6 46) 24948 24 4 15
    64 325 65 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
