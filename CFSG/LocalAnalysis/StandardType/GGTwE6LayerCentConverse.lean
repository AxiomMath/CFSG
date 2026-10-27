module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LayerRestTwo

public section

namespace CFSG.StandardType

namespace LayerCores

theorem layerCentre_of_isSubCoreFamily {S : Type*} [Group S] {H : Subgroup S} {β : Type}
    {T : β → Subgroup S} (h : IsSubCoreFamily H T) :
    ∀ z ∈ CFSG.Open.GLALayer H, (∀ y ∈ CFSG.Open.GLALayer H, z * y = y * z) → z ^ 2 = 1 →
      z = 1 := by
  obtain ⟨hle, hsub, hqs, ⟨k, hk⟩, hz⟩ := h
  have hL : CFSG.Open.GLALayer H = ⨆ c, T c := by
    refine le_antisymm (sSup_le fun K hK => ?_) (iSup_le fun c => le_sSup ?_)
    · have hq : CFSG.IsQuasisimple K :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hK.2.2
      have hp := LayerFacts.ggCommutator_eq_of_isQuasisimple hq
      exact (LayerFacts.ggDer_of_perfect hp k).symm.le.trans
        ((LayerFacts.ggDer_mono hK.1 k).trans hk)
    · exact ⟨hle c, CFSG.Assembly.isSubnormal_iff_open.1 (hsub c),
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 (hqs c)⟩
  intro z hz' hzc hz2
  rw [hL] at hz' hzc
  exact hz z hz' hzc hz2

end LayerCores

section Converse

theorem ggTwE6LayerCentInvolTrivial_of_coreRestTwo (h : GGTwE6InndiagCoreRestTwoInput) :
    GGTwE6LayerCentInvolTrivial := by
  intro f hf p hp hp2 A hA hAc hAD hn hs
  obtain ⟨_, T, hT⟩ := h f hf p hp hp2 A hA hAc hAD hn hs
  exact LayerCores.layerCentre_of_isSubCoreFamily hT

end Converse

section Equivalence

theorem ggTwE6InndiagCoreRestInput_iff_layerCentre :
    GGTwE6InndiagCoreRestInput ↔ GGTwE6LayerCentInvolTrivial :=
  ⟨fun h => ggTwE6LayerCentInvolTrivial_of_coreRestTwo (ggTwE6InndiagCoreRestTwoInput_of_rest h),
    ggTwE6InndiagCoreRestInput_of_layerCentre⟩

end Equivalence

end CFSG.StandardType
