module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C00
import Certificates.Kernel.J4TreeNode.W
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7861 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 0 :=
  chunk_facts tabs_ok sx_ok 0 rec00 chk00_all edge00 fun _ => global_ok

end Certificates
