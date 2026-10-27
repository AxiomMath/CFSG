module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Fix
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSU)
open Item434Kit Item434Alt

namespace Item434SmallTwoIVU62

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_u62_27 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 6 2 1)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have h27' : Nat.card h.layerStar = 27 := h27
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases h.card_layerStar with h9 | ⟨-, hZ⟩
    · omega
    · exact hZ
  set e : layer G ⧸ Subgroup.center (layer G) ≃* P6 := e₀.trans u6Equiv with he
  have hAe := isElemAbelian_map_quotConj h e
  have hA27 : Nat.card (A.map (quotConj e)) = 27 := by
    rw [Item434Spor.card_map_quotConj h e, h27']
  obtain ⟨Bs, hBsA, hBs9, D, hD, hD81, hfix⟩ := exists_fixed_e81 hAe hA27
  have hBg : 9 ≤ Nat.card (A ⊓ Bs.comap (quotConj e) : Subgroup G) :=
    hBs9.trans (card_le_card_inf_comap e hBsA)
  exact false_of_fixed h hZ e (B := A ⊓ Bs.comap (quotConj e)) inf_le_left hBg hD hD81
    (fun b hb d hd => hfix _ hb.2 d hd)

end Item434SmallTwoIVU62

section Families


theorem item434SmallTwoIV_U62_27 : Item434SmallTwoIV_U62_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoIVU62.false_of_u62_27 hc e₀ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
