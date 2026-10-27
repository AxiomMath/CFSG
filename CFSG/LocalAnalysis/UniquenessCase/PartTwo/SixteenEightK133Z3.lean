module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Ker
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Normal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_z3_rk6 (h : S16kBase D V₀ V L hV)
    (hZ : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6) : False := by
  have h3 : 3 ∈ D.sig := s16k_z3_three_mem_sig h hZ hrk
  have hk : 4 ≤ CFSG.pRank 3 (D.M : Subgroup G) := by
    rw [UC6.groupPRank_eq_pRank]
    exact h.std.hx.four_le h.std.h4 3 h3
  obtain ⟨A, hAM, hA, hA4⟩ :=
    c23_exists_elemAbelian_card_pow (p := 3) Nat.prime_three (M := D.M) (k := 4) hk
  by_cases hN : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      ((barSub V₀ V hV A : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV)))
  · exact s16k_false_of_z3_normal h hZ hrk hAM hA hA4 hN
  · exact s16k_false_of_z3_ker h hZ hrk hAM hA hA4 hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
