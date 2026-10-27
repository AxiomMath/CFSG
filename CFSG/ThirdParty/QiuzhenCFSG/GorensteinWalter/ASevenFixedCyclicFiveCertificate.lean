module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
public theorem a7_fixed_cyclic_five_certificate :
    ∀ x : ASevenCertificateGroup,
      (x ≠ 1 ∧ x ^ 5 = 1 ∧
        fixedSpanPow 5 x (a7a * x * a7a⁻¹)) →
      a7t * x = x * a7t := by
  unfold fixedSpanPow
  decide

end CFSG.GorensteinWalter
