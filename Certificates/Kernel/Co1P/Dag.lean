module

public import Certificates.Kernel.Co1P.Defs
public import Certificates.Data.Kernel.Co1BSteps
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Sporadic.Co1Patterson.GraphTreeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KD.Co1B CFSG.KD.Co1P CFSG.KC.Co1P
  CertificateChecks.KernelCo1Cover

theorem bray_chk : dagOK [R0, R1, getL oneK IRS 23] CFSG.Sporadic.Co1Block.twoAD1 BRS59 BRIS59 = true := by
  quickRfl

theorem gdag_p : prefixK gBaseK GDS = true := by quickRfl

theorem gdag_i : invsK GDS GDIS = true := by quickRfl

theorem gdag_s0 : stepsPre GDS GDIS (GWL.take 43) (lenL gBaseK) = true := by quickRfl

theorem gdag_s1 : stepsPre GDS GDIS ((GWL.drop 43).take 43) (lenL gBaseK + 43) = true := by quickRfl

theorem gdag_s2 : stepsPre GDS GDIS (((GWL.drop 43).drop 43).take 43) (lenL gBaseK + 43 + 43) = true := by quickRfl

theorem gdag_s3 : stepsK GDS GDIS (((GWL.drop 43).drop 43).drop 43) (lenL gBaseK + 43 + 43 + 43) = true := by quickRfl

theorem gdag_chk : dagOK gBaseK GWL GDS GDIS = true := by
  have hs : stepsK GDS GDIS GWL (lenL gBaseK) = true :=
    stepsK_cut GDS GDIS GWL (lenL gBaseK) 43 (Nat.le_of_ble_eq_true (by quickRfl)) gdag_s0
      (stepsK_cut GDS GDIS (GWL.drop 43) (lenL gBaseK + 43) 43 (Nat.le_of_ble_eq_true (by quickRfl)) gdag_s1
      (stepsK_cut GDS GDIS ((GWL.drop 43).drop 43) (lenL gBaseK + 43 + 43) 43 (Nat.le_of_ble_eq_true (by quickRfl)) gdag_s2
      (gdag_s3)))
  unfold dagOK
  rw [gdag_p, gdag_i, hs]
  rfl

theorem gwords_text : CFSG.Sporadic.Co1Patterson.Native.gWordsText = String.ofList (wordsC GWL) := by
  str_lits CFSG.Sporadic.Co1Patterson.Native.gWordsText
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

end CertificateChecks.KernelCo1P

end
