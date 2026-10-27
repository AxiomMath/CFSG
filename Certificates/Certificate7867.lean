module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C06
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7867 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 6 :=
  chunk_facts tabs_ok sx_ok 6 rec06 chk06_all edge06 fun h => absurd h (by decide)

end Certificates
