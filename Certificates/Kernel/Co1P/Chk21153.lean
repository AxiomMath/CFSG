module

public import Certificates.Kernel.Co1P.Defs21153
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits
import CFSG.Certificates.Kernel.Common.StrLitsProj
public import Certificates.Data.Kernel.Co1PText

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KLie.CT CFSG.Sporadic.Co1Patterson.Native

theorem text0n : lvl3Text0.1 = String.ofList (natsC (nodesL 0)) := by
  str_lits_fst lvl3Text0
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem text0p : lvl3Text0.2 = String.ofList (natsC (parsL 0)) := by
  str_lits_snd lvl3Text0
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem text1n : lvl3Text1.1 = String.ofList (natsC (nodesL 1)) := by
  str_lits_fst lvl3Text1
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem text1p : lvl3Text1.2 = String.ofList (natsC (parsL 1)) := by
  str_lits_snd lvl3Text1
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem wit0_text : lvl3WitText0 = String.ofList (pairsC (witL 0)) := by
  str_lits lvl3WitText0
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem wit1_text : lvl3WitText1 = String.ofList (pairsC (witL 1)) := by
  str_lits lvl3WitText1
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem masks_ok : andB (Nat.beq (bitsOf (nodesL 0)) (MSt 0)) (Nat.beq (bitsOf (nodesL 1)) (MSt 1)) = true := by
  quickRfl

end CertificateChecks.KernelCo1P

end
