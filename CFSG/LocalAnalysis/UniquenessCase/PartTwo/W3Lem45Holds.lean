module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveSub

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise
open CFSG.LocalAnalysis.WeakClosure81
  (fourFiveQuotCompFAS fourFive_quotCompFAS_of_inFGroup fourFive_whole_subgroup)

theorem fourFive_quotCompFAS_of_compFactorAutInF {G : Type} [Group G] [Finite G] {j : ℕ}
    {H S : Subgroup G} (h : CompFactorAutInF j H S) :
    fourFiveQuotCompFAS j ↥H (S.subgroupOf H) := by
  refine fourFive_quotCompFAS_of_inFGroup fun Y' hY' => ?_
  obtain ⟨Y, hYH, rfl⟩ : ∃ Y : Subgroup G, Y ≤ H ∧ Y.subgroupOf H = Y' :=
    ⟨Y'.map H.subtype, Subgroup.map_subtype_le Y',
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y'⟩
  exact h Y hYH hY'

theorem w3Lem45_2_holds (G : Type) [Group G] [Finite G] : W3Lem45_2 G :=
  fun H S j Ω hj hS hΩ hF =>
    fourFive_whole_subgroup hj hS hΩ (fourFive_quotCompFAS_of_compFactorAutInF hF)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
