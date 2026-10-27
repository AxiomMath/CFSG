module

public import Certificates.Kernel.Co1B.KC25172
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.Bfs24513

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KC.Enum

theorem kZ4 : allN 4096 (fun i => zOK (ST.P (4096 * 4 + i))) = true := by quickRfl
theorem kZ5 : allN 4096 (fun i => zOK (ST.P (4096 * 5 + i))) = true := by quickRfl
theorem kZ6 : allN 4096 (fun i => zOK (ST.P (4096 * 6 + i))) = true := by quickRfl
theorem kZ7 : allN 4096 (fun i => zOK (ST.P (4096 * 7 + i))) = true := by quickRfl

end CertificateChecks.KernelCo1B.Syl2B

end
