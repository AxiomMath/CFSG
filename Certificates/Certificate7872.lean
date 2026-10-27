module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C11
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7872 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 11 :=
  chunk_facts tabs_ok sx_ok 11 rec11 chk11_all edge11 fun h => absurd h (by decide)

end Certificates
