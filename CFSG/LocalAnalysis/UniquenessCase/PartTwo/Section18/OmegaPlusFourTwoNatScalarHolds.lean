module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourTwoNatInvHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourTwoNatScalarIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.Pair
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem k_OmegaPlusFour_twoNat_scalar_holds : K_OmegaPlusFour_twoNat_scalar := by
  intro W _ _ hW X hX hsum ht
  obtain ⟨I, hIbot, hItop, hIN, hIind, hIsup⟩ := exists_pair_of_sumOfNat_two hsum
  obtain ⟨t, htN, htord, hm⟩ := ht
  by_cases hiso : IsoMod X (I 0) (I 1)
  · exact k_OmegaPlusFour_twoNat_scalar_of_isoMod (sumOfNatIsoMod_of_pair hIind hIsup hIN hiso)
  · have ht2 : t ^ 2 = 1 := by
      rw [← htord]
      exact pow_orderOf_eq_one t
    exact (false_of_involution_of_not_isoMod hIbot hItop hIN hiso htN ht2 hm).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
