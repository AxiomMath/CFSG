module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.FieldAutCatalog
import CFSG.LocalAnalysis.UniquenessCase.UC6K332Bridge
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3Chev2
import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.RankThree.PartTwo.Sec4.RonanK432
open CFSG.LocalAnalysis.AGL81TheoremCD.Section8 (fixedData_of_catalog)

theorem goodRow_of_pRank_le_one
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : CFSG.Open.IsCatalogGroup S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1) :
    GoodRow S := by
  by_cases h3 : 3 ∣ Nat.card S
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 h3
    have hxc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
    have hr1 : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1 :=
      le_antisymm hr (N588A.one_le_pRank Nat.prime_three le_top hxc)
    exact ⟨fun z _ _ => Or.inl hr1, outerRow_of_three_dvd_of_fixed (center_eq_bot_of_simple hs hna)
      fun α hα hout =>
        (fixedData_of_catalog hs hna hcat hr1 α hα hout).1⟩
  · exact ⟨fun z hz _ => absurd (hz ▸ orderOf_dvd_natCard z) h3, fun h => absurd h h3⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
