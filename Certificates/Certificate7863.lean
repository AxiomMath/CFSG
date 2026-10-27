module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C02
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7863 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 2 :=
  chunk_facts tabs_ok sx_ok 2 rec02 chk02_all edge02 fun h => absurd h (by decide)

end Certificates
