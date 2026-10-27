module

public import Certificates.Kernel.Co1ThreeK.DataP
public import Certificates.Kernel.Co1ThreeK.Letters
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1B CFSG.KS.SporSch.M24

theorem kKD : dagWK KD.M KD.MI 2 89 CS.KW = true := by quickRfl

theorem kKB : (Nat.beq (KD.M 0) (L.M 9) && Nat.beq (KD.M 1) (L.M 10)) = true := by quickRfl

theorem kNB : Nat.beq (mulWK (KD.M 87) (L.M 5)) (mulWK (R.M 1) (KD.M 87)) = true := by quickRfl

theorem kNC : Nat.beq (mulWK (KD.M 88) (L.M 4)) (mulWK (R.M 0) (KD.M 88)) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
