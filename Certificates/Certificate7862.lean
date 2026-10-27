module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C01
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7862 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 1 :=
  chunk_facts tabs_ok sx_ok 1 rec01 chk01_all edge01 fun h => absurd h (by decide)

end Certificates
