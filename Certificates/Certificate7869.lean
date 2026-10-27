module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C08
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7869 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 8 :=
  chunk_facts tabs_ok sx_ok 8 rec08 chk08_all edge08 fun h => absurd h (by decide)

end Certificates
