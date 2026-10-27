module

public import Certificates.Kernel.Co1ThreeK.LeafGens
public import Certificates.Kernel.Co1B.XB17591
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Co1Leaf CertificateChecks.KernelCo1B.Bound17591

theorem kD10 : leafK XB (GD 1 0) LD.P7 LD.W7 LD.S7 LD.B7 LD.T7 = true := by quickRfl

theorem kD11 : leafK XB (GD 1 1) LD.P8 LD.W8 LD.S8 LD.B8 LD.T8 = true := by quickRfl

theorem kD12 : leafK XB (GD 1 2) LD.P9 LD.W9 LD.S9 LD.B9 LD.T9 = true := by quickRfl

theorem kD13 : leafK XB (GD 1 3) LD.P10 LD.W10 LD.S10 LD.B10 LD.T10 = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
