module

public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowOf
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowOfK
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowLeaf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepED4LowClose_of_cells (hcells : GGDepED4LowCells) : GGDepED4LowClose := by
  intro hFix hFixK hPZ G _ _ p k _ B Bs x L D J y K hH hxL hp3 hk hCard labJ labX hJΛ hXΛ hJl hXl
    hrow htag hJcard hRG hHL hHK hA
  exact ggDepED4Low_leaf hPZ hk hp3 hH hJΛ hXΛ hJl hXl hrow htag hCard hJcard hRG hcells
    (Or.inl ⟨rfl, ggDepED4LowCfg_of_aligned hFix hFixK hH hxL hk hp3 hCard (fun _ => hHL)
      (fun _ => hHK) hA⟩)

theorem ggDepED4LowCloseK_of_cells (hcells : GGDepED4LowCells) : GGDepED4LowCloseK := by
  intro hFix hFixK hPZ G _ _ p _ B Bs x L D J y K hH hyK hp3 hCard labJ labX hJΛ hXΛ hJl hXl hrow
    htag hJcard hRG hHK hHL hA
  exact ggDepED4Low_leaf hPZ (Or.inl rfl) hp3 hH hJΛ hXΛ hJl hXl hrow htag hCard hJcard hRG hcells
    (Or.inr ⟨rfl, ggDepED4LowCfg_of_alignedK (k := 1) hFix hFixK hH hyK hp3 hCard (fun _ => hHK)
      (fun _ => hHL) hA⟩)

end CFSG.StandardType

end
