module

public import Certificates.Kernel.Co1I301.Chk810305
public import Certificates.Data.Kernel.SporSch.Co1BfsSegF
public import CFSG.Certificates.Kernel.Common.EachTrue
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1I301

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KC.Co1I301 CFSG.KLie.CT
  CFSG.KS.SporSch.M24 CertificateChecks.KernelCo1P

@[expose] noncomputable def BKM (l : Nat) : Nat := getL 0 BK l

@[expose] noncomputable def BIKM (l : Nat) : Nat := getL 0 BIK l

theorem kDTh : (Nat.beq DT.L0.N 8960 && bfsHeadK DT.L0.P DT.L0.PAR DT.L0.LAB 8960 140 64 DK) =
    true := by
  quickRfl

#kc_each CertificateChecks.KernelCo1I301.ch810305d s
  (fun i => bfsSegFK (ctStepK BKM BIKM) 8 8961 8960 DT.L0.P DT.L0.PAR DT.L0.LAB DT.L0.W DT.L0.S 140 i)
  0 64

#kc_forall_chunks kDTs (fun i => bfsSegFK (ctStepK BKM BIKM) 8 8961 8960 DT.L0.P DT.L0.PAR DT.L0.LAB
  DT.L0.W DT.L0.S 140 i = true) 64 CertificateChecks.KernelCo1I301.ch810305d.s 1

theorem negDTh : notB (bfsHeadK DT.L0.P DT.L0.PAR DT.L0.LAB 8960 140 63 DK) = true := by
  quickRfl

theorem negDTs : notB (bfsSegFK (ctStepK BKM BIKM) 8 8961 8960 DT.L0.P (fun k => DT.L0.PAR k + 1)
    DT.L0.LAB DT.L0.W DT.L0.S 140 0) = true := by
  quickRfl

theorem kRec : (Nat.beq KI.RP.length 8959 && Nat.beq KI.RL.length 8959 &&
    eqListK DT.L0.PAR KI.RP 1 && eqListK DT.L0.LAB KI.RL 1) = true := by
  quickRfl

theorem kOrb : orbChk BK BIK 8 DK 8960 (zipK KI.RP KI.RL) = true := by quickRfl

theorem negOrb : notB (orbChk BK BIK 8 DK 8960 (zipK (KI.RP.map (· + 1)) KI.RL)) = true := by
  quickRfl

end CertificateChecks.KernelCo1I301

end
