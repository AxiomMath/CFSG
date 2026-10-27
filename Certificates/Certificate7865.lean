module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C04
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7865 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 4 :=
  chunk_facts tabs_ok sx_ok 4 rec04 chk04_all edge04 fun h => absurd h (by decide)

end Certificates
