module

public import Certificates.Kernel.Co1P.Defs21156
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

theorem loc_ok : orbChk GE GEI 6 (ptE 202) 8 (recsT loc202Masks) = true ∧
    orbChk GE GEI 6 (ptE 2348) 8 (recsT loc2348Masks) = true ∧
    orbChk GE GEI 6 (ptE 3940) 8 (recsT loc3940Masks) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem t192_ok : orbChk GE GEI 6 (ptE 35) 8 (recsT t192Masks) = true := by quickRfl

theorem pins_ok : pinsOK = true := by quickRfl

theorem tri_small : triSmallK = true := by quickRfl

theorem tri_cone : triConeK = true := by quickRfl

end CertificateChecks.KernelCo1P

end
