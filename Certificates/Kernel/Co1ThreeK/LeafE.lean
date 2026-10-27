module

public import Certificates.Kernel.Co1ThreeK.LeafGens
public import Certificates.Kernel.Co1B.XB17591
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Co1Leaf CertificateChecks.KernelCo1B.Bound17591

theorem kE0 : leafK XB (GE 0) LD.P0 LD.W0 LD.S0 LD.B0 LD.T0 = true := by quickRfl

theorem kE1 : leafK XB (GE 1) LD.P1 LD.W1 LD.S1 LD.B1 [] = true := by quickRfl

theorem kE2 : leafK XB (GE 2) LD.P2 LD.W2 LD.S2 LD.B2 LD.T2 = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
