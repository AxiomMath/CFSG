module

public import CFSG.LocalAnalysis.WeakClosure81.EightSeven
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1)

variable {G : Type} [Group G] [Finite G]

theorem rk_le_add_of_isE_not_le_normalizer {V H T A K : Subgroup G} {i j : ℕ} (hV7 : Hyp7 V)
    (hH0 : IsCalH0 V H) (hT : IsSylowIn 2 T (H ⊓ normalizer (V : Set G)))
    (hA : A ∈ E3.gammaSet V i T) (hK : E1.IsE j H T A K)
    (hKM : ¬ K ≤ normalizer (V : Set G)) : rk ↥V ≤ j + i := by
  by_contra hle
  rw [not_le] at hle
  have hA0 : A ∈ E3.gammaSet V i T := hA
  obtain ⟨hAT, g, hAg, -⟩ := hA0
  have hVne : V ≠ ⊥ := by
    intro hbot
    have h2 := hV7.2.1
    rw [hbot, Subgroup.card_bot] at h2
    omega
  exact hKM (le_normalizer_of_isE hV7.1 hV7.2.2 hVne hH0 hT hAT ⟨g, hAg⟩ hK
    (inf_centralizer_eSub_ne_bot_of_isE hV7.1 hH0 hT hA hle hK))

end CFSG.LocalAnalysis.WeakClosure81

end
