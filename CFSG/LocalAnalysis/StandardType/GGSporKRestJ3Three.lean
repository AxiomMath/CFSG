module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestOverP
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverA6

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRestAsch86J3Three_holds :
    SporKRestAsch86J3Three := by
  intro S Y hY hSY
  haveI : Finite (TauCeti.CFSGIndex.sporadic .J3).Group :=
    CFSG.Sporadic.Presentation.J3.finite_card_le.1
  have hJ : Nonempty ((TauCeti.CFSGIndex.sporadic .J3).Group ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := ⟨MulEquiv.refl _⟩
  rcases (CFSG.AGLEmbedding.j3CoverFacts _ hJ).2 S Y hSY with hle | htop
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI := CFSG.AGLEmbedding.isSolvable_normalizer_of_facts S.isPGroup'
      (CFSG.AGLEmbedding.kFactJ3Sylow _ hJ S)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  · exact absurd htop hY

theorem sporKRest_coverOrUnmarked_J3_3 :
    SporKRestCoverOrUnmarked 3 (TauCeti.CFSGIndex.sporadic .J3).Group :=
  ggSporKRest_coverOrUnmarked_J3_3_of_asch86 sporKRestAsch86J3Three_holds

end CFSG.StandardType.SporadicShape

end
