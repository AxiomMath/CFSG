module

public import Certificates.Kernel.Co1B.KC25172
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.Bfs24513

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KC.Enum

theorem kZ0 : allN 4096 (fun i => zOK (ST.P (4096 * 0 + i))) = true := by quickRfl
theorem kZ1 : allN 4096 (fun i => zOK (ST.P (4096 * 1 + i))) = true := by quickRfl
theorem kZ2 : allN 4096 (fun i => zOK (ST.P (4096 * 2 + i))) = true := by quickRfl
theorem kZ3 : allN 4096 (fun i => zOK (ST.P (4096 * 3 + i))) = true := by quickRfl

end CertificateChecks.KernelCo1B.Syl2B

end
