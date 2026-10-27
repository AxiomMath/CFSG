module

public import Certificates.Kernel.Co1P.Defs21235
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1P.Chk21158

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1Patterson.TwistNative

theorem tab_chk : allN 256 (fun v => andB (Nat.beq (fget TW0 v 8) (actWord (genWords.getD 0 []) v))
    (Nat.beq (fget TW1 v 8) (actWord (genWords.getD 1 []) v))) = true := by quickRfl

theorem wordsW_ok : (treePts actK 2 (wKey w0Basis) recsW).2 = true := by quickRfl

theorem recsW_pin : recsEqK recW recsW 0 = true := by quickRfl

theorem recsW_len : recsW.length = 20159 := by decide

theorem vec_chk : (wVecs.all fun v => actWord [0, 0, 0, 0, 0, 0] v == v) = true := by quickRfl

theorem orb_chk : andB (eqK (repK 0) (qwW 1)) (PQ.any fun y => eqK (wK 64) y) = true := by quickRfl

end CertificateChecks.KernelCo1P

end
