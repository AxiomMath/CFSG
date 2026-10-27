module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenConjugateSpan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Intermediate

variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_commSub_lBar_sup_fixV_eq_top (c : S168e3Ctx D V₀ V L hV) :
    commSub ⊤ (lBar V₀ V hV L) ⊔ fixV (lBar V₀ V hV L) = ⊤ := by
  obtain ⟨t, -, -, -, -, hconc⟩ := c.conc
  exact commSub_sup_fixV_eq_top_of_conc4_136W hconc

end Intermediate

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
