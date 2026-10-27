module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
import Certificates.Kernel.J4TreeNode.Facts
import Certificates.Kernel.J4TreeNode.C05
import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace Certificates

open CFSG.KC.J4TreeN

theorem certificate7866 : CFSG.ASVolI.burnsideJ4NP_TreeChunkFacts 5 :=
  chunk_facts tabs_ok sx_ok 5 rec05 chk05_all edge05 fun h => absurd h (by decide)

end Certificates
