module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGSixE6A24Centre
public import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltqZc_lieModel_of_hasLabel_E6 {X : Type} [Group X]
    (hX : GGHasLabel ⟨.E6, 0, 1⟩ X) : CFSG.Blueprint.LieModel X .E6 0 2 1 := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  refine CFSG.Blueprint.LieModel.of_mulEquiv e.symm ?_
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl⟩,
    untwistedChevalleyModel_largeEven .E6 hK⟩)

theorem ggE6TwoCenterBot_holds :
    GGE6TwoCenterBot := by
  intro K _ _ hperf hlab
  exact ggSixE6A24_center_eq_bot K hperf (ltqZc_lieModel_of_hasLabel_E6 hlab)

end CFSG.StandardType

end
