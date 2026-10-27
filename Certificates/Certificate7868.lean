module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C07
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7868 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 7 :=
  chunk_facts tabs_ok sx_ok 7 rec07 chk07_all edge07 fun h => absurd h (by decide)

end Certificates
