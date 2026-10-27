module

public import Certificates.Kernel.Co1P.Defs21151
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

theorem sub45_ok : sub45K = true := by quickRfl

theorem fibS_ok : orbChk GE GEI 6 (repK 6) 9 (recsT fib6Masks) = true ∧
    orbChk GE GEI 6 (repK 7) 8 (recsT fib7Masks) = true ∧
    orbChk GE GEI 6 (repK 9) 11 (recsT fib9Masks) = true ∧
    orbChk GE GEI 6 (repK 4) 11 (recsT fib4Masks) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem cntQ_ok : Nat.beq (sumN 5 (cntK 270 fun i => mem4 (conjQ i (repK 5)))) 9 = true := by quickRfl

theorem cnt_sums : andB (Nat.beq (sumN 197 (getL 0 CN4)) 45) (Nat.beq (sumN 197 (getL 0 CN8)) 25) = true := by
  quickRfl

theorem recs4C_pin : recsEqK r4C (recsT orb4cMasks) 0 = true := by quickRfl

theorem recsF8_pin : recsEqK rF8 (recsT fib8Masks) 0 = true := by quickRfl

theorem recsF5_pin : recsEqK rF5 (recsT fib5Masks) 0 = true := by quickRfl

theorem fibS_len : Nat.beq (recsT fib6Masks).length 383 = true ∧ Nat.beq (recsT fib7Masks).length 191 = true ∧
    Nat.beq (recsT fib9Masks).length 2047 = true ∧ Nat.beq (recsT fib4Masks).length 2047 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem recs4C_lenB : Nat.beq (recsT orb4cMasks).length 34559 = true := by quickRfl

theorem recsF8_lenB : Nat.beq (recsT fib8Masks).length 24575 = true := by quickRfl

theorem recsF5_lenB : Nat.beq (recsT fib5Masks).length 16383 = true := by quickRfl

end CertificateChecks.KernelCo1P

end
