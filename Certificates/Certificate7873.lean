module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C12
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7873 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 12 :=
  chunk_facts tabs_ok sx_ok 12 rec12 chk12_all edge12 fun h => absurd h (by decide)

end Certificates
