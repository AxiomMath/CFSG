module

public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictColIds
import Certificates.Kernel.J4TreeCol.Glue
public import CFSG.Milestones.ASVolI.C31.J4NP.TreeDefs
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictDefs

public section

namespace Certificates

theorem certificate7902 : ∀ k ∈ CFSG.ASVolI.burnsideJ4NP_colIds2,
    CFSG.ASVolI.burnsideJ4NP_VerdictW (CFSG.ASVolI.burnsideJ4NP_Wv k) :=
  CFSG.KC.J4TreeCol.c7902

end Certificates
