module

public import Certificates.Kernel.Co1ThreeK.DataH
public import Certificates.Kernel.Co1ThreeK.Forest
public import Certificates.Data.Kernel.Co1Three.Dual
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl

@[expose] noncomputable def ND : List (Nat × List Nat) := List.zip [6, 7, 8] CH.DR

theorem kHyp : (Nat.beq (nzLen ND) 3 && dualsK 3 6 NF ND && eqLK CH.RT [243, 81, 190] &&
    forestK 3 6 ND CH.RT CH.DP CH.FT) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
