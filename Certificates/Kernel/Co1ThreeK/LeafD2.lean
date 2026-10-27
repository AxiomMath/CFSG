module

public import Certificates.Kernel.Co1ThreeK.LeafGens
public import Certificates.Kernel.Co1B.XB17591
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Co1Leaf CertificateChecks.KernelCo1B.Bound17591

theorem kD20 : leafK XB (GD 2 0) LD.P11 LD.W11 LD.S11 LD.B11 LD.T11 = true := by quickRfl

theorem kD21 : leafK XB (GD 2 1) LD.P12 LD.W12 LD.S12 LD.B12 LD.T12 = true := by quickRfl

theorem kD22 : leafK XB (GD 2 2) LD.P13 LD.W13 LD.S13 LD.B13 LD.T13 = true := by quickRfl

theorem kD23 : leafK XB (GD 2 3) LD.P14 LD.W14 LD.S14 LD.B14 LD.T14 = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
