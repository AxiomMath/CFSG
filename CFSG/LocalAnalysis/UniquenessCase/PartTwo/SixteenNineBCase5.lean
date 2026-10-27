module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBNatOm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case5_good (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLM : L ≤ D.M) (h5 : Case168_5 D V₀ V hV L) (n N : ℕ) :
    s16n9bGood (Mbar D.M V₀ V hV) 3 n N := by
  obtain ⟨-, -, hN, -⟩ := h5
  refine s16n9bGood_of_forall_fix fun z hz => ?_
  obtain ⟨ψ, hψ, hord, hfix⟩ := s16n9b_natOmegaPlus_fix hN hz
  exact ⟨ψ, barSub_mono V₀ V hV hLM hψ, hord, hfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
