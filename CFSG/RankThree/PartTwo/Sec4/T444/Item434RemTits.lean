module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LieType.Multipliers.Tits

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Sporadic.Schreier.Tits

namespace Item434RemTits

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_tits
    (h : Ctx434Core G A M Q)
    (hL : IsSmallTwoOtherTits (layer G ⧸ Subgroup.center (layer G))) : False := by
  obtain ⟨eD⟩ := titsModelEquiv (layer G ⧸ Subgroup.center (layer G)) 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits hL)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Tits.multiplier_of_mulEquiv_titsD eD
    have h1 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (layer G ⧸ Subgroup.center (layer G))) = 1 := by
      rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
        Nat.card_congr eM.toEquiv, Nat.card_unique]
    have h2 := CFSG.RankThree.PartTwo.KFacts.KS44.card_center_dvd_card_hopfMultiplier
      h.isQuasisimple
    rw [h1, Nat.dvd_one] at h2
    exact Subgroup.card_eq_one.mp h2
  have hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer titsD) := by
    rw [card_outer_titsD]
    norm_num
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · exact Item434SporGen.false_of_kill9 h eD hout titsD_center
      (fun _ hPe hP9 => Or.inr (noSignalizer hPe hP9)) h9
  · obtain ⟨P, hPe, hPc, -⟩ := Item434SmallTwoOther.exists_inner h eD hout titsD_center
    rw [h27] at hPc
    exact false_of_e27 hPe hPc

end Item434RemTits

section Families


theorem item434SmallTwoOtherAtTits :
    Item434SmallTwoOtherAtTits := by
  intro _ _ _ _ _ G _ _ _ _ _ A M Q hc hL
  exact (Item434RemTits.false_of_tits hc hL).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
