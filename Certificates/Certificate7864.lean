module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C03
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7864 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 3 :=
  chunk_facts tabs_ok sx_ok 3 rec03 chk03_all edge03 fun h => absurd h (by decide)

end Certificates
