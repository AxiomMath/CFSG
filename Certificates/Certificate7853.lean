
module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4Aff2A.Check
import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.J4Aff2A.Sound
import CFSG.Milestones.ASVolI.C31.J4NP.Is2AAffBase

public section

namespace Certificates

open CFSG.KC.J4TreeN CFSG.KC.J4Aff2A

theorem certificate7853 : ∀ x ∈ CFSG.Sporadic.J4.Hj, x * x = 1 → x ≠ 1 →
    (CFSG.ASVolI.burnsideJ4NP_Is2A x ↔
      CFSG.ASVolI.burnsideJ4NP_treeTest (CFSG.ASVolI.burnsideJ4NP_encJ x) = true) :=
  fun _ hx hsq hne => (CFSG.ASVolI.burnsideJ4NP_Is2A_iff_isConj _).trans
    (is2A_iff_treeTest_H tabs_ok sx_ok ch7853_all hx hsq hne)

end Certificates
