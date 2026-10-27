module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeOm4NatA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_om4_natBar {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L) :
    NatOmegaPlus (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 4 2 := by
  obtain ⟨t, htm, ht2, htne, htrk, hW⟩ := c.conc
  obtain ⟨K, hK, g, hg, hne, hL, hK2, hT⟩ := s168e3_exists_tensor_of_isOmegaPlus_two hW h.1
  rw [show commSub ⊤ (lBar V₀ V hV L) = ⊤ from wTil_eq_top_of_case163_2 c.conc h.2.2] at hT
  exact natOmegaPlus_of_natTensor (le_refl 2) hT

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
