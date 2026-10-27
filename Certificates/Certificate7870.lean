module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C09
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7870 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 9 :=
  chunk_facts tabs_ok sx_ok 9 rec09 chk09_all edge09 fun h => absurd h (by decide)

end Certificates
