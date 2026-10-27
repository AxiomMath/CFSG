module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightMod
public import CFSG.LocalAnalysis.WeakClosure81.W19EBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_modData {H E F : Subgroup G} (hH : Group.IsSolvable ↥H) (hEH : E ≤ H)
    (hE : IsElemAbelian 2 E) (hFE : F < E) (hEn : H ≤ normalizer (E : Set G))
    (hFn : H ≤ normalizer (F : Set G))
    (hirr : ∀ U : Subgroup G, F ≤ U → U ≤ E → H ≤ normalizer (U : Set G) → U = F ∨ U = E) :
    Nonempty (ModData H E F) := by
  obtain ⟨W, _, _, _, ρ, ι, h1, h2, h3, h4, h5, h6, h7⟩ := exists_rep hH hEH hE hFE hEn hFn hirr
  exact ⟨⟨W, ρ, ι, h1, h2, h3, h4, h5, h6, h7⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

end
