module

public import Certificates.Kernel.Co1P.Defs21151
public import Certificates.Kernel.Co1P.RecsZ
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.TreeKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

theorem sub45_ok : sub45K = true := by quickRfl

theorem cntQ_ok : Nat.beq (sumN 5 (cntK 270 fun i => mem4 (conjQ i (repK 5)))) 9 = true := by quickRfl

theorem cnt_sums : andB (Nat.beq (sumN 197 (getL 0 CN4)) 45) (Nat.beq (sumN 197 (getL 0 CN8)) 25) = true := by
  quickRfl

theorem recs4C_ok :
    andB (andB (recsEqK r4C (recsZ orb4cMasks) 0) (Nat.beq (recsZ orb4cMasks).length 34559))
      (andB (treePts (hsAct BK) 8 oneK (recsZ orb4cMasks)).2
        (treePts (hisAct BIK) 8 oneK (recsZ orb4cMasks)).2) = true := by
  quickRfl

theorem recs4C_pin : recsEqK r4C (recsT orb4cMasks) 0 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recs4C_ok).1).1

theorem recs4C_lenB : Nat.beq (recsT orb4cMasks).length 34559 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recs4C_ok).1).2

theorem walk4C_hs : (treePts (hsAct BK) 8 oneK (recsT orb4cMasks)).2 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recs4C_ok).2).1

theorem walk4C_his : (treePts (hisAct BIK) 8 oneK (recsT orb4cMasks)).2 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recs4C_ok).2).2

end CertificateChecks.KernelCo1P

end
