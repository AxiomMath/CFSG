module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C13
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7874 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 13 :=
  chunk_facts tabs_ok sx_ok 13 rec13 chk13_all edge13 fun h => absurd h (by decide)

end Certificates
