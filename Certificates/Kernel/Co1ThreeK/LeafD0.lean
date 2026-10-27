module

public import Certificates.Kernel.Co1ThreeK.LeafGens
public import Certificates.Kernel.Co1B.XB17591
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Co1Leaf CertificateChecks.KernelCo1B.Bound17591

theorem kD00 : leafK XB (GD 0 0) LD.P3 LD.W3 LD.S3 LD.B3 LD.T3 = true := by quickRfl

theorem kD01 : leafK XB (GD 0 1) LD.P4 LD.W4 LD.S4 LD.B4 LD.T4 = true := by quickRfl

theorem kD02 : leafK XB (GD 0 2) LD.P5 LD.W5 LD.S5 LD.B5 LD.T5 = true := by quickRfl

theorem kD03 : leafK XB (GD 0 3) LD.P6 LD.W6 LD.S6 LD.B6 LD.T6 = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
