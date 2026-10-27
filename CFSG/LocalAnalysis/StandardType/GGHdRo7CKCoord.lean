module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordA
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordB
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordC

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_kcoord_holds :
    C2KCoordLeaf := by
  intro hRig hLB G _ _ p B Bs x L D J y K hH hfact hrow
  obtain ⟨n, hy, hx, τ, hp3, hn, h0, hmodel, hmem⟩ := hdRo7CKCoordAux_model hRig hH hrow
  obtain ⟨i, j, hi, hj, hij, hsupp⟩ :=
    hdRo7CKCoordAux_support hRig hLB hH hrow n hy hx τ hp3 hn h0 hmodel hmem
  obtain ⟨τ', h0', hmodel', c, hc⟩ :=
    hdRo7CKCoordAux_normalize p hp3 Bs K n τ ⟨y, hy⟩ ⟨x, hx⟩ h0 hmodel i j hi hj hij hsupp
  exact ⟨n, hy, hx, τ', hp3, hn, h0', hmodel', c, hc⟩

end CFSG.StandardType.HdRo7C

end
