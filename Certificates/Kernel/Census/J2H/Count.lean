module

public import Certificates.Kernel.Census.J2H.Chains
public import Certificates.Kernel.J2Cover.KerChains
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.J2H
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelJ2H

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2Cover CFSG.KC.J2H
open CertificateChecks.KernelJ2Cover

theorem s0_canon : allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (S0C.S j)) = true := by
  quickRfl

theorem v_canon : allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (VC.S j)) = true := by
  quickRfl

theorem s0_countB : Nat.beq (prodCnt 315 9 3 CRT.LR CRT.TR (commAllK 4 S0C.S)) 2 = true := by
  quickRfl

theorem v_countB : Nat.beq (prodCnt 315 9 3 CRT.LR CRT.TR (commAllK 4 VC.S)) 2 = true := by
  quickRfl

theorem s0_count : prodCnt 315 9 3 CRT.LR CRT.TR (commAllK 4 S0C.S) = 2 :=
  Nat.eq_of_beq_eq_true s0_countB

theorem v_count : prodCnt 315 9 3 CRT.LR CRT.TR (commAllK 4 VC.S) = 2 :=
  Nat.eq_of_beq_eq_true v_countB

end CertificateChecks.KernelJ2H
