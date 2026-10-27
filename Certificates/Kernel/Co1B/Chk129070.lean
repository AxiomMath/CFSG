module

public import Certificates.Kernel.Co1B.Dag129070
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.SporSch.Co1Cent
public import Certificates.Data.Kernel.SporSch.Co1Heis
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1B
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1F0Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C129070

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1F2 CFSG.KD.Co1B CFSG.KS.Raw
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

@[expose] noncomputable def IA : Nat := getL CFSG.KC.Co1B.oneK IRS 23

@[expose] noncomputable def PBf : Nat := F1.M (f0IB - 1)

@[expose] noncomputable def PS1 : Nat := F1.M (f0S1 - 1)

@[expose] noncomputable def PS2 : Nat := F1.M (f0S2 - 1)

theorem kb : (Nat.beq (F1.M 0) SA && Nat.beq (F1.M 1) SB && Nat.beq (F1.M 2) IA) = true := by
  quickRfl
theorem kN : (Nat.beq F1.N 96 && Nat.beq F2.N 29) = true := by quickRfl
theorem kD1 : dagWK F1.M F1.MI 3 F1.N (f0D1.map encWordK) = true := by quickRfl
theorem kI : (f0Bidx.all (fun j => decide (3 < j) && decide (j ≤ F1.N)) && decide (f0IB ≤ F1.N) &&
    decide (f0S1 ≤ F1.N) && decide (f0S2 ≤ F1.N)) = true := by quickRfl
theorem kBind : bindK F1.M F2.M f0Bidx = true := by quickRfl
theorem kD2 : dagWK F2.M F2.MI f0Bidx.length F2.N (f0D2.map encWordK) = true := by quickRfl
theorem kC : (commK F1.M IA (f0Bidx.take 8) && commK F1.M PBf (f0Bidx.drop 8)) = true := by
  quickRfl

theorem kM : (Nat.beq (mulK IA PBf) (mulK PBf IA) && Nat.beq (mulK PBf PBf) idM &&
    (unpack 24 24 PBf != unpack 24 24 idM) && (unpack 24 24 PBf != unpack 24 24 IA) &&
    Nat.beq (mulK PS1 IA) (mulK PBf PS1) && Nat.beq (mulK PS1 PBf) (mulK IA PS1) &&
    Nat.beq (mulK PS2 PBf) (mulK (mulK IA PBf) PS2) &&
    Nat.beq (mulK PS2 (mulK IA PBf)) (mulK PBf PS2) &&
    Nat.beq (F2.M 27) SA && Nat.beq (F2.M 28) SB) = true := by
  quickRfl

end CertificateChecks.KernelCo1B.C129070

end
