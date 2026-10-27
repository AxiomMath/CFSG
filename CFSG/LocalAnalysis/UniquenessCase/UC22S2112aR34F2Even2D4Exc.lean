module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Cases
import CFSG.LocalAnalysis.UniquenessCase.UC22D4NoSwapInput
import CFSG.LocalAnalysis.UniquenessCase.UC22D4FunRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Uniq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)


theorem uc22ExcTwoFunWeak_trialityD4 : UC22ExcTwoFunWeak .trialityD4 := by
  intro X _ _ _ p hp hp7 hX
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hadm : StatedLieAdmissible .trialityD4 0 p 1 := ⟨hp, le_rfl, rfl⟩
  refine ⟨fun S K₁ K₂ h₁ h₂ hne hcomm =>
    Or.inr (uc22s2112r34_d4_noSwapInput hp (by omega) hX S h₁ h₂ hne hcomm),
    fun K K' hK hK' x hx hxr hx5 hxp => ?_⟩
  have hK₁ : IsFundamentalOver (p ^ 1) K := by
    rwa [pow_one]
  have hK₂ : IsFundamentalOver (p ^ 1) K' := by
    rwa [pow_one]
  rcases d4_fund_equiv_sl2 hp2 hadm hX hK₁ with hL | hS
  · have h := d4_pRank_centralizer_of_mem_long hp2 hadm hX hK₁ hL (mem_inf.1 hx).1
    exact Or.inr (by omega)
  rcases d4_fund_equiv_sl2 hp2 hadm hX hK₂ with hL' | hS'
  · have h := d4_pRank_centralizer_of_mem_long hp2 hadm hX hK₂ hL' (mem_inf.1 hx).2
    exact Or.inr (by omega)
  obtain ⟨eK⟩ := hS
  obtain ⟨eK'⟩ := hS'
  exact uc22d4_fund_eq_or_rank_of_short (by omega) hadm hX hK₁ hK₂ eK eK' hx hxr hx5 hxp

end CFSG.LocalAnalysis.UniquenessCase.UC22
