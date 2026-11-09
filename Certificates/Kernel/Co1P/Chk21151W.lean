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

theorem fibS_okZ : orbChk GE GEI 6 (repK 6) 9 (recsZ fib6Masks) = true ∧
    orbChk GE GEI 6 (repK 7) 8 (recsZ fib7Masks) = true ∧
    orbChk GE GEI 6 (repK 9) 11 (recsZ fib9Masks) = true ∧
    orbChk GE GEI 6 (repK 4) 11 (recsZ fib4Masks) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem fibS_ok : orbChk GE GEI 6 (repK 6) 9 (recsT fib6Masks) = true ∧
    orbChk GE GEI 6 (repK 7) 8 (recsT fib7Masks) = true ∧
    orbChk GE GEI 6 (repK 9) 11 (recsT fib9Masks) = true ∧
    orbChk GE GEI 6 (repK 4) 11 (recsT fib4Masks) = true := by
  simp only [recsT_eq_recsZ]
  exact fibS_okZ

theorem fibS_len : Nat.beq (recsT fib6Masks).length 383 = true ∧ Nat.beq (recsT fib7Masks).length 191 = true ∧
    Nat.beq (recsT fib9Masks).length 2047 = true ∧ Nat.beq (recsT fib4Masks).length 2047 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem recsF8_ok :
    andB (andB (recsEqK rF8 (recsZ fib8Masks) 0) (Nat.beq (recsZ fib8Masks).length 24575))
      (andB (treePts (hsAct GE) 6 oneK (recsZ fib8Masks)).2
        (treePts (hisAct GEI) 6 oneK (recsZ fib8Masks)).2) = true := by
  quickRfl

theorem recsF5_ok :
    andB (andB (recsEqK rF5 (recsZ fib5Masks) 0) (Nat.beq (recsZ fib5Masks).length 16383))
      (andB (treePts (hsAct GZ) 6 oneK (recsZ fib5Masks)).2
        (treePts (hisAct GZI) 6 oneK (recsZ fib5Masks)).2) = true := by
  quickRfl

theorem recsF8_pin : recsEqK rF8 (recsT fib8Masks) 0 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recsF8_ok).1).1

theorem recsF5_pin : recsEqK rF5 (recsT fib5Masks) 0 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recsF5_ok).1).1

theorem recsF8_lenB : Nat.beq (recsT fib8Masks).length 24575 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recsF8_ok).1).2

theorem recsF5_lenB : Nat.beq (recsT fib5Masks).length 16383 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recsF5_ok).1).2

theorem walkF8_hs : (treePts (hsAct GE) 6 oneK (recsT fib8Masks)).2 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recsF8_ok).2).1

theorem walkF8_his : (treePts (hisAct GEI) 6 oneK (recsT fib8Masks)).2 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recsF8_ok).2).2

theorem walkF5_hs : (treePts (hsAct GZ) 6 oneK (recsT fib5Masks)).2 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recsF5_ok).2).1

theorem walkF5_his : (treePts (hisAct GZI) 6 oneK (recsT fib5Masks)).2 = true := by
  rw [recsT_eq_recsZ]
  exact (andB_true (andB_true recsF5_ok).2).2

end CertificateChecks.KernelCo1P

end
