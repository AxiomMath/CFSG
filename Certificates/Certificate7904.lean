module

public import Certificates.Data.CFSGNative.J4Tree.VerdictData
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictColNode
import Certificates.Kernel.J4TreeCol.Glue7904

public section

namespace Certificates

theorem certificate7904 : ∀ d ∈ CFSG.J4Tree.Native.Col.colUnionNodes,
    Subgroup.normalizer (CFSG.ASVolI.burnsideJ4NP_Wv d.k : Set CFSG.Sporadic.J4.J) ≤
      Subgroup.normalizer ((Subgroup.closure (CFSG.ASVolI.burnsideJ4NP_colO d) :
        Subgroup CFSG.Sporadic.J4.J) : Set CFSG.Sporadic.J4.J) :=
  CFSG.KC.J4TreeCol.c7904

end Certificates
