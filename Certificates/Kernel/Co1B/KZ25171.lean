module

public import Certificates.Kernel.Co1B.KC25171
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.Bfs2047

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C25171

open CFSG.KC.Enum

theorem kZ : allN 2048 (fun i => zOKC (C2047.QT.P i)) = true := by quickRfl

end CertificateChecks.KernelCo1B.C25171

end
