module

public import Certificates.Kernel.Co1B.Dag129070
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.SporSch.Co1Heis
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1B
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1DispBCCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C1037002

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1F2 CFSG.KD.Co1B
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CertificateChecks.KernelCo1B.C129070

@[expose] noncomputable def IA : Nat := getL CFSG.KC.Co1B.oneK IRS 23

@[expose] noncomputable def IC : Nat := getL CFSG.KC.Co1B.oneK IRS 51

theorem kb : (Nat.beq (BC.M 0) SA && Nat.beq (BC.M 1) SB && Nat.beq (BC.M 2) IA &&
    Nat.beq BC.N 551) = true := by
  quickRfl
theorem kD : dagWK BC.M BC.MI 3 BC.N ((dispHeis ++ dispBC).map encWordK) = true := by quickRfl
theorem kHB : heisK SA (BC.M 547) (BC.MI 547) (BC.M 548) (BC.MI 548) = true := by quickRfl
theorem kHC : heisK IC (BC.M 549) (BC.MI 549) (BC.M 550) (BC.MI 550) = true := by quickRfl

end CertificateChecks.KernelCo1B.C1037002

end
