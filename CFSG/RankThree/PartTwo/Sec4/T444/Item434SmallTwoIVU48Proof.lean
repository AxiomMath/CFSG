module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Inner
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Outer
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSU)
open Item434Kit Item434Alt

namespace Item434SmallTwoIVU48

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_u48_27 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 4 2 3)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have h27' : Nat.card h.layerStar = 27 := h27
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases h.card_layerStar with h9 | ⟨-, hZ⟩
    · omega
    · exact hZ
  set e : layer G ⧸ Subgroup.center (layer G) ≃* SU4 := e₀.trans equivSU4 with he
  have hA27 : Nat.card (A.map (quotConj e)) = 27 := by
    rw [Item434Spor.card_map_quotConj h e, h27']
  by_cases hout : ∃ α ∈ A.map (quotConj e), fieldFactor4 α ≠ 1
  · exact false_of_outer h hZ e hA27 hout
  · push Not at hout
    exact false_of_inner h e hA27 fun α hα => mem_range_conj_of_fieldFactor4_eq_one (hout α hα)

end Item434SmallTwoIVU48

section Families


theorem item434SmallTwoIV_U48_27 : Item434SmallTwoIV_U48_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoIVU48.false_of_u48_27 hc e₀ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
