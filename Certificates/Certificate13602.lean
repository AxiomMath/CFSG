module

public import CFSG.Sporadic.HNSchreier.FALocal
import Certificates.Kernel.SporCovLane.HNWitGlue

public section

namespace Certificates

open CFSG.Sporadic.HNSchreier in
theorem certificate13602 : (g3J ^ 6) ^ 5 = 1 ∧ g3J ^ 6 ≠ 1 ∧
    ∀ j < 4, c3J 0 * g3J ^ 6 ≠ (g3J ^ 6) ^ (j + 1) * c3J 0 :=
  CFSG.KD.SporCovLane.HNWit.hn_witness

end Certificates
