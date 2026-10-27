module

public import Certificates.Kernel.Co1ThreeK.LeafGens
public import Certificates.Kernel.Co1B.XB17591
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Co1Leaf CertificateChecks.KernelCo1B.Bound17591

theorem kD30 : leafK XB (GD 3 0) LD.P15 LD.W15 LD.S15 LD.B15 LD.T15 = true := by quickRfl

theorem kD31 : leafK XB (GD 3 1) LD.P16 LD.W16 LD.S16 LD.B16 LD.T16 = true := by quickRfl

theorem kD32 : leafK XB (GD 3 2) LD.P17 LD.W17 LD.S17 LD.B17 LD.T17 = true := by quickRfl

theorem kD33 : leafK XB (GD 3 3) LD.P18 LD.W18 LD.S18 LD.B18 LD.T18 = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
