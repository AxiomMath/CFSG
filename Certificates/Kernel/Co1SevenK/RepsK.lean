module

public import Certificates.Kernel.Co1SevenK.Syl
public import Certificates.Data.TabMSevenCo1Reps
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KC.Co1B Timmesfeld.Co1Seven
  CFSG.HardMathSupport.Dickson.I271.TabMSeven

@[expose] noncomputable def F1K : Nat := mulWK (powWK (D.M 68) 3) (D.M 69)

@[expose] noncomputable def F2K : Nat := powWK (D.M 70) 7

theorem kReps : (unpack 24 24 SK == repSevenA && unpack 24 24 TK == repSevenB) = true := by
  quickRfl

theorem kOrd4 : (Nat.beq (powWK F1K 4) idM && unpack 24 24 (powWK F1K 2) != unpack 24 24 idM &&
    Nat.beq (powWK F2K 4) idM && unpack 24 24 (powWK F2K 2) != unpack 24 24 idM) = true := by
  quickRfl

end CertificateChecks.KernelCo1SevenK

end
