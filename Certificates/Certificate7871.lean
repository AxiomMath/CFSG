module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C10
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7871 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 10 :=
  chunk_facts tabs_ok sx_ok 10 rec10 chk10_all edge10 fun h => absurd h (by decide)

end Certificates
