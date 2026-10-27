module

public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.SporSch.Co1Stab
public import Certificates.Data.Kernel.Co1B
public import CFSG.RankThree.PartOne.SPOR.Co1SylowData
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.Co1Syl5.In
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co1.GenDag

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelCo1Syl5.S CertificateChecks.KernelCo1Syl5.sylDag

namespace CertificateChecks.KernelCo1Syl5

open CFSG.KS.SporSch.M24 CFSG.KC.Co1F2 CFSG.KD.Co1B CFSG.RankThree.PartOne.SPOR
open CFSG.KC.Co1B (oneK)

theorem kB : (Nat.beq (S.M 0) SA && Nat.beq (S.M 1) SB && Nat.beq (S.M 2) (getL oneK IRS 23) &&
    Nat.beq (S.M 3) (getL oneK IRS 51)) = true := by quickRfl

theorem kD : dagIK S.M S.MI 4 S.N co1SylowDerivs = true := by quickRfl

theorem kN : Nat.beq S.N 42 = true := by quickRfl

end CertificateChecks.KernelCo1Syl5

end
