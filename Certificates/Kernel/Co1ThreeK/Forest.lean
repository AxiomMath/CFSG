module

public import Certificates.Kernel.Co1ThreeK.DataF
public import Certificates.Data.Kernel.Co1Three.Slp
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl

@[expose] noncomputable def NF : List (Nat × List Nat) := List.zip [6, 7, 8] (CS.NR.take 3)

theorem kForest : (Nat.beq (nzLen NF) 3 && eqLK CF.RT [81, 243, 327] &&
    forestK 3 6 NF CF.RT CF.DP CF.FT) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
