module

public import Certificates.Kernel.Co1B.Code24511
public import Certificates.Kernel.Co1B.Dag24513
public import Certificates.Kernel.Co1B.Bfs24513
public import Certificates.Data.Kernel.SporSch.Co1CtStar
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.H24511

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CertificateChecks.KernelCo1B.Syl2B

theorem kF2 : allN 4096 (fun i => fourConjK S2.M S2.MI 10 (ST.P (4096 * 2 + i))
    (CC (4096 * 2 + i))) = true := by quickRfl
theorem kF3 : allN 4096 (fun i => fourConjK S2.M S2.MI 10 (ST.P (4096 * 3 + i))
    (CC (4096 * 3 + i))) = true := by quickRfl

end CertificateChecks.KernelCo1B.H24511

end
