module

public import Certificates.Kernel.Co1B.Data17597
public import Certificates.Kernel.Co1M.Regs10071
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Kernel.SporSch.Co1.ElemDag
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1BW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Fix17597

open CFSG.KLie.CT CFSG.KC.Co1F2 CFSG.KC.Co1B CertificateChecks.KernelCo1M

theorem m0_chk : Nat.beq (mulWK (getL 0 cmRP71 27) (getL 0 cmRP71 70)) D0.M = true := by quickRfl

theorem m1_chk : Nat.beq (CertificateChecks.KernelCo1ThreeK.R.M 0) D1.M = true := by quickRfl

theorem m2_chk : Nat.beq (CertificateChecks.KernelCo1ThreeK.R.M 2) D2.M = true := by quickRfl

theorem m3_chk : Nat.beq (mulWK (mulWK (CertificateChecks.KernelSporSch.Co1Elem.AF 1)
    (CertificateChecks.KernelSporSch.Co1Elem.AF 4)) (CertificateChecks.KernelSporSch.Co1Elem.AF 5))
    D3.M = true := by quickRfl

theorem fix0_chk : fixK 24 (trK 24 D0.M) 0 D0.F D0.Y 12 4096 0 = true := by quickRfl

theorem fix1_chk : fixK 24 (trK 24 D1.M) 0 D1.F D1.Y 6 64 0 = true := by quickRfl

theorem fix2_chk : fixK 24 (trK 24 D2.M) 0 D2.F D2.Y 8 256 0 = true := by quickRfl

theorem fix3_chk : fixK 24 (trK 24 D3.M) 0 D3.F D3.Y 0 1 0 = true := by quickRfl

end CertificateChecks.KernelCo1B.Fix17597

end
