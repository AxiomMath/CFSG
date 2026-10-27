module

public import CFSG.RankThree.PartOne.S15K.Row2Types
public import CFSG.RankThree.PartOne.S15K.OrthTypes

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem layerModelData_two_three {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (h13 : Sec13Facts G p A c L E)
    (hout : Outcome152Two p E A (lieGenerated p E) ∨ Outcome152Three p E A (lieGenerated p E)) :
    LayerModelData p E (lieGenerated p E) := by
  rcases hout with h | h
  · exact layerModelData_row2 h15.h12 h13 h
  · exact layerModelData_row3 h15.h12 h13 h

theorem layerBlockModels :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
      (Outcome152Two p E A (lieGenerated p E) ∨ Outcome152Three p E A (lieGenerated p E)) →
      ∀ b ∈ E, b ≠ 1 → ∀ Y ∈ thetaComponentsAt p b, Y ≤ lieGenerated p E → BlockModel p ↥Y := by
  intro G _ _ p A c L E h15 hF h13 hout b hb hb1 Y hY hYI
  exact (layerModelData_two_three h15 h13 hout).blockModel_of_mem_thetaComponentsAt h15.h12.prime hb
    hb1 hY hYI

theorem layerTypes :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
      (Outcome152Two p E A (lieGenerated p E) ∨ Outcome152Three p E A (lieGenerated p E)) →
      ∀ b ∈ E, b ≠ 1 → ∀ Y ∈ thetaComponentsAt p b, Y ≤ lieGenerated p E → BlockType p ↥Y := by
  intro G _ _ p A c L E h15 hF h13 hout b hb hb1 Y hY hYI
  exact (layerBlockModels G p A c L E h15 hF h13 hout b hb hb1 Y hY hYI).blockType

end CFSG.RankThree.PartOne.S15K
