module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Rechoice

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_z3_normal (h : S16kBase D V₀ V L hV)
    (hZ : IsCyclicOrd ↥(lBar V₀ V hV L) 3) (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6)
    {A : Subgroup G} (hAM : A ≤ D.M) (hA : IsElemAbelian 3 A) (hA4 : Nat.card A = 3 ^ 4)
    (hN : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      ((barSub V₀ V hV A : Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV)))) :
    False := by
  obtain ⟨E, hE⟩ := s16k_z3_frame h hZ hrk hAM hA hA4 hN
  exact s16k_false_of_frame h hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
