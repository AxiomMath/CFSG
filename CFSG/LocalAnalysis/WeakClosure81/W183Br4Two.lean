module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Red
public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Case1
public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Case2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem br4_false_of_two_good {X S : Type} [Group X] [Finite X]
    [Group S] (hX : CFSG.pRank 3 X ≤ 3) (θ : X →* S) (hθ : Function.Surjective θ)
    {A₁ A₂ : Subgroup S} (h : Br4TwoSimple S A₁ A₂) (g₁ : Br4Good ↥A₁) (g₂ : Br4Good ↥A₂) :
    False := by
  haveI : Finite S := Finite.of_surjective θ hθ
  obtain ⟨Y, _, _, θ', hθ', hQ, hperf, hr⟩ := br4_exists_cover h g₁.three_dvd g₂.three_dvd θ hθ
  by_cases hC : Subgroup.centralizer (θ'.ker : Set Y) ≤ θ'.ker
  · exact br4_false_case_one h g₁ g₂ θ' hθ' hQ hperf (hr.trans hX) hC
  · exact br4_false_case_two h g₁ g₂ θ' hθ' hQ (hr.trans hX) hC

end CFSG.LocalAnalysis.WeakClosure81

end
