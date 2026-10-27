module

public import Certificates.Kernel.Co3T.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co3T.EnumQ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.KC.Co3TK CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CertificateChecks.KernelSpor

theorem kLines : Nat.beq TT.lines 36 = true := by quickRfl

theorem kPerm : allN 36 (fun k => permB 276 9 (TT.L k)) = true := by quickRfl

theorem kD : dK TT.L DE = true := by quickRfl

theorem kSiftQ : allN 4 (fun k => sAll (TT.L k)) = true := by quickRfl

theorem kSiftD : allN 5 (fun i => sAll (TT.L (4 + i))) = true := by quickRfl

theorem kSiftY : sAll (TT.L 9) = true := by quickRfl

theorem kSiftC : allN 3 (fun k => sAll (EC.G k)) = true := by quickRfl

theorem kEQ : (Nat.beq EQ.ng 4 && Nat.beq EQ.N 2187 &&
    allN 4 (fun k => Nat.beq (EQ.G k) (TT.L k))) = true := by quickRfl

theorem kEC : (Nat.beq EC.ng 3 && Nat.beq EC.N 4536 &&
    allN 3 (fun k => Nat.beq (EC.G k) (TT.L (9 + k)))) = true := by quickRfl

theorem kECkeys : CFSG.KC.BfsPin.keysSK 276 9 CFSG.Sporadic.Schreier.Co3.co3ChainBaseArr.toList EC.N
    EC.T EC.SK = true := by quickRfl

theorem kOrth : orthK CK = true := by quickRfl

theorem kTr : allN 12 trK = true := by quickRfl

theorem kY : (Nat.beq (pw 276 9 (TT.L 9) 3) (pidn 276 9) && !Nat.beq (TT.L 9) (pidn 276 9)) =
    true := by quickRfl

theorem kRels : relsK 276 9 3 Co3C.BP (TT.L 9) 7 yRels = true := by quickRfl

theorem kComm : commK 276 9 3 (TT.L 9) EC.G = true := by quickRfl

theorem kRc : Nat.beq (rcnt (Co3C.LR 0)) 276 = true := by quickRfl

end CertificateChecks.KernelCo3T

end
