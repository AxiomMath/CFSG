module

public import Certificates.Kernel.B3S3.HSEnum
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.B3S3KCR
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Data.Kernel.Misc.ChainTailOrb
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelB3S3.HS OD "Certificates/Kernel/B3S3/data/hsorb.bin" 2 4 18046 10773998975602721836

namespace CertificateChecks.KernelB3S3.HS

@[expose] noncomputable def RI (k : ℕ) : ℕ := OD k

@[expose] noncomputable def EK (k : ℕ) : ℕ := OD (Nat.add 3850 k)

@[expose] noncomputable def RB (j : ℕ) : ℕ := OD (Nat.add 7700 j)

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.KC.Misc.Clos (allR)

@[expose] noncomputable def RI1 (k : ℕ) : ℕ := OD (Nat.add 7702 k)

@[expose] noncomputable def EK1 (k : ℕ) : ℕ := OD (Nat.add 7822 k)

@[expose] noncomputable def RB1 (j : ℕ) : ℕ := OD (Nat.add 7942 j)

theorem q0a : Nat.blt (RB 0) (rcnt (C0.LR 0)) = true := by quickRfl

theorem q0b : Nat.beq (rpt 12 (mask 12) (C0.LR 0) (RB 0)) (pg 12 (mask 12) C0.BP 0) = true := by
  quickRfl

theorem rc1 : Nat.beq (rcnt (C0.LR 1)) 120 = true := by quickRfl

theorem rep0 : repBranchK1 3850 12 C0.LR C0.TR C0.BP (XC.F 0) (pw 3850 12 (XC.F 0)) hsS3C0Rels
    E0.N E0.T 6 (RB 0) (RB1 0) = true := by quickRfl

@[expose] noncomputable def ob1 (k : ℕ) : Bool :=
  orbRelK1 3850 12 C0.LR C0.TR C0.BP (pw 3850 12 (XC.F 0)) hsS3C0Rels E0.N E0.T (RB 0) 1 RB1 RI1
    EK1 k

theorem ob1_0 : allR 0 120 ob1 = true := by quickRfl

theorem rep1 : repBranchK 3850 12 C0.LR C0.TR C0.BP (XC.F 0) (pw 3850 12 (XC.F 0)) hsS3C0Rels
    E0.N E0.T 6 (RB 1) = true := by quickRfl

@[expose] noncomputable def ob (k : ℕ) : Bool :=
  orbRelK 3850 12 C0.LR C0.BP (pw 3850 12 (XC.F 0)) hsS3C0Rels E0.N E0.T 2 RB RI EK k

@[expose] noncomputable def CR (i : ℕ) : ℕ := OD (Nat.add 7943 i)

@[expose] noncomputable def CG (i : ℕ) : ℕ := OD (Nat.add 8303 i)

@[expose] noncomputable def WJ2 (i : ℕ) : ℕ := OD (Nat.add 8663 i)

@[expose] noncomputable def cv (i : ℕ) : Bool :=
  convCR 3850 12 E0.N E0.T [2, 5] [1] WJ2 WR CR CG i

theorem ob_0 : allR 0 350 ob = true := by quickRfl
theorem ob_1 : allR 350 350 ob = true := by quickRfl
theorem ob_2 : allR 700 350 ob = true := by quickRfl
theorem ob_3 : allR 1050 350 ob = true := by quickRfl
theorem ob_4 : allR 1400 350 ob = true := by quickRfl
theorem ob_5 : allR 1750 350 ob = true := by quickRfl
theorem ob_6 : allR 2100 350 ob = true := by quickRfl
theorem ob_7 : allR 2450 350 ob = true := by quickRfl
theorem ob_8 : allR 2800 350 ob = true := by quickRfl
theorem ob_9 : allR 3150 350 ob = true := by quickRfl
theorem ob_10 : allR 3500 350 ob = true := by quickRfl

theorem cv_0 : allR 0 30 cv = true := by quickRfl
theorem cv_1 : allR 30 30 cv = true := by quickRfl
theorem cv_2 : allR 60 30 cv = true := by quickRfl
theorem cv_3 : allR 90 30 cv = true := by quickRfl
theorem cv_4 : allR 120 30 cv = true := by quickRfl
theorem cv_5 : allR 150 30 cv = true := by quickRfl
theorem cv_6 : allR 180 30 cv = true := by quickRfl
theorem cv_7 : allR 210 30 cv = true := by quickRfl
theorem cv_8 : allR 240 30 cv = true := by quickRfl
theorem cv_9 : allR 270 30 cv = true := by quickRfl
theorem cv_10 : allR 300 30 cv = true := by quickRfl
theorem cv_11 : allR 330 30 cv = true := by quickRfl

end CertificateChecks.KernelB3S3.HS

end
