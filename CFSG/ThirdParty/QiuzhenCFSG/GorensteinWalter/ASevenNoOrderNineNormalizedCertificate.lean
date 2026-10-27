module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
public theorem a7_no_order_nine_normalized_by_t_certificate :
    ∀ x : A7OrderThree,
      ((x : ASevenCertificateGroup) * a7a = a7a * (x : ASevenCertificateGroup) ∧
        (x : ASevenCertificateGroup) ≠ a7a ∧
        (x : ASevenCertificateGroup) ≠ a7a ^ 2 ∧
        fixedSpanThree x a7a
          (a7t * (x : ASevenCertificateGroup) * a7t⁻¹)) → False := by
  unfold fixedSpanThree
  decide

end CFSG.GorensteinWalter
