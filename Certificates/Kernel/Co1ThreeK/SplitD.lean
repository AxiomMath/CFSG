module

public import Certificates.Kernel.Co1ThreeK.LeafGens
public import Certificates.Data.Kernel.Co1Three.Split
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Co1Leaf CFSG.KLie.CT

theorem kSplitD : planeK [R.M 2] (PD 0) (PD 1) = true := by quickRfl

theorem kSplitC : allN 4 (fun a => planeK [R.M 2, eltWK [PD 0, PD 1] (LD.DV.getD a [])]
    (PD (2 + 2 * a)) (PD (3 + 2 * a))) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
