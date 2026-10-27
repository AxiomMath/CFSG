module

public import Certificates.Kernel.Co1B.Dag129070
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.SporSch.Co1Heis
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1B
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1DispCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C129071

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1F2 CFSG.KD.Co1B
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CertificateChecks.KernelCo1B.C129070

@[expose] noncomputable def IA : Nat := getL CFSG.KC.Co1B.oneK IRS 23

@[expose] noncomputable def IC : Nat := getL CFSG.KC.Co1B.oneK IRS 51

theorem kbH : (Nat.beq (H.M 0) SA && Nat.beq (H.M 1) SB && Nat.beq (H.M 2) IA &&
    Nat.beq H.N 391) = true := by
  quickRfl
theorem kDH : dagWK H.M H.MI 3 H.N (dispHeis.map encWordK) = true := by quickRfl
theorem kHeis : heisK IA (H.M 389) (H.MI 389) (H.M 390) (H.MI 390) = true := by quickRfl

theorem kbC : (Nat.beq (C.M 0) SA && Nat.beq (C.M 1) SB && Nat.beq (C.M 2) IC &&
    Nat.beq C.N 5) = true := by
  quickRfl
theorem kDC : dagWK C.M C.MI 3 C.N (dispDihD.map encWordK) = true := by quickRfl
theorem kDihC : dihK IC (C.M 3) (C.MI 3) = true := by quickRfl
theorem kDihA : dihK SA (C.M 4) (C.MI 4) = true := by quickRfl

end CertificateChecks.KernelCo1B.C129071

end
