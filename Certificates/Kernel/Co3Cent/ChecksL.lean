module

public import Certificates.Kernel.Co3Cent.EnumL
public import Certificates.Kernel.Co3Cent.CentLData
public import Certificates.Kernel.Co3Cent.Hex
public import Certificates.Kernel.Co3T.EnumC
public import Certificates.Data.Kernel.HeDihK
public import Certificates.Data.Kernel.K426K
public import Certificates.Data.Kernel.PGrp
public import Certificates.Data.Kernel.OrbRow.Cent
public import Certificates.Data.L28Presentation
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co3Cent

open CFSG.KC.Enum CFSG.KC.HeDih CFSG.KC.K426K CFSG.KC.PGrp CFSG.KC.OrbRow
open CFSG.HardMathSupport.Dickson.I271.L28Presentation CertificateChecks.KernelCo3Cent

theorem ch17370_lg : bAnd(Nat.beq (EL.G 0) (CertificateChecks.KernelCo3Cent.CH.F 36),
    bAnd(Nat.beq (EL.G 1) (CertificateChecks.KernelCo3Cent.CH.F 37),
    bAnd(Nat.beq (EL.G 0) (posWordK 276 9 CertificateChecks.KernelCo3T.EC.G (getLs WL 0)),
    bAnd(Nat.beq (EL.G 1) (posWordK 276 9 CertificateChecks.KernelCo3T.EC.G (getLs WL 1)),
    bAnd(allN 2 (fun l => lettersK 3 7 (getLs WL l)),
    bAnd(Nat.beq EL.ng 2, Nat.beq EL.N 504)))))) = true := by
  quickRfl

theorem ch17370_ld : derivedLeK 276 9 EL.N CertificateChecks.KernelCo3T.EC.ng EL.ng EL.T EL.S
    CertificateChecks.KernelCo3T.EC.G EL.G = true := by
  quickRfl

theorem ch17370_lr :
    l28Words.all (fun wd => Nat.beq (evalWK 276 9 EL.G wd) (pidn 276 9)) = true := by
  quickRfl

end CFSG.KD.Co3Cent

end
