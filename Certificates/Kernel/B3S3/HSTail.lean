module

public import Certificates.Kernel.B3S3.HSEnum
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.HS

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.KC.Misc.Clos (allR)

@[expose] noncomputable def br (k : ℕ) : Bool :=
  ptailBranchK 3850 12 C0.LR C0.TR C0.BP (XC.F 0) (pw 3850 12 (XC.F 0)) hsS3C0Rels E0.N E0.T 6 k

@[expose] noncomputable def cv (i : ℕ) : Bool := convAt 3850 12 E0.N E0.T [2, 5] [1] WJ WR i

theorem br_0 : allR 0 350 br = true := by quickRfl
theorem br_1 : allR 350 350 br = true := by quickRfl
theorem br_2 : allR 700 350 br = true := by quickRfl
theorem br_3 : allR 1050 350 br = true := by quickRfl
theorem br_4 : allR 1400 350 br = true := by quickRfl
theorem br_5 : allR 1750 350 br = true := by quickRfl
theorem br_6 : allR 2100 350 br = true := by quickRfl
theorem br_7 : allR 2450 350 br = true := by quickRfl
theorem br_8 : allR 2800 350 br = true := by quickRfl
theorem br_9 : allR 3150 350 br = true := by quickRfl
theorem br_10 : allR 3500 350 br = true := by quickRfl

theorem cv_0 : allR 0 60 cv = true := by quickRfl
theorem cv_1 : allR 60 60 cv = true := by quickRfl
theorem cv_2 : allR 120 60 cv = true := by quickRfl
theorem cv_3 : allR 180 60 cv = true := by quickRfl
theorem cv_4 : allR 240 60 cv = true := by quickRfl
theorem cv_5 : allR 300 60 cv = true := by quickRfl

end CertificateChecks.KernelB3S3.HS

end
