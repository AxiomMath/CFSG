module

public import Certificates.Data.Kernel.Co1PairsRep
public import Certificates.Kernel.Co1Pairs.Data
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Kernel.SporSch.Co1.ElemDag
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pairs

open CFSG.KC.Co1Pairs CFSG.KD.Co1Pairs CertificateChecks.KernelCo1ThreeK
open CertificateChecks.KernelSporSch.Co1Elem (AF)

theorem ch214033r :
    (Nat.beq (eltK [AF 0, AF 1, AF 2, AF 3, AF 4, AF 5] [1, 0, 0, 0, 0, 0]) R0 &&
      Nat.beq (eltK [AF 0, AF 1, AF 2, AF 3, AF 4, AF 5] [0, 1, 0, 0, 0, 0]) R1 &&
      Nat.beq (eltK [AF 0, AF 1, AF 2, AF 3, AF 4, AF 5] [1, 1, 0, 0, 0, 0]) R2) = true := by
  quickRfl

theorem ch214033t : (threeK R0 && threeK R1 && threeK R2 && threeK (R.M 2)) = true := by quickRfl

theorem ch214033k : (neK K0 && neK K1 && neK K2 && neK K3 && neK K4 && neK K5 && neK K6 &&
    neK K7 && neK K8 && neK K9 && neK (CFSG.KC.Co1B.mulWK K0 K1)) = true := by quickRfl

end CertificateChecks.KernelCo1Pairs

end
