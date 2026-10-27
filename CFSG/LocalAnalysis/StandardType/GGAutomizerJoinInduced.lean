module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

theorem ggAutomizerJoin_le_ggInduced_top {G : Type} [Group G] {Bs : Subgroup G}
    (L : Subgroup G) (𝒦 : Finset (Subgroup G)) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs := by
  intro φ hφ
  rw [ggAutomizerJoin] at hφ
  exact mem_ggInduced_top_of_mem_ggAutomizer
    (sup_le (ggAutomizer_mono Bs le_top)
      (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top) hφ)

end CFSG.StandardType

end
