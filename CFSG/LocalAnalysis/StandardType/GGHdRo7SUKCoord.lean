module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUCoordDefs

import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordG

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem su_kcoord_holds :
    SUKCoordLeaf := by
  intro hRig hLB G instG instFin p B Bs x L D J y K hH instPrime hrow
  obtain ⟨hy, τ, hp, hm, h3, hτ, hmodel⟩ := hdRo7SUKCoordAux_model hH hRig hrow
  exact ⟨hdRo7SUKCoordAux_rowRank hrow, hy, τ, hp, hm, h3, hτ, hmodel⟩

end CFSG.StandardType.HdRo7SU
