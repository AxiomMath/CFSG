module

public import CFSG.LocalAnalysis.StandardType.GGLayerCentInvolCores

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.GLTheoremA

private theorem finite_mulAut_oddLayer (G : Type) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun α : MulAut G => (α : G → G)) (fun _ _ h => MulEquiv.ext (congrFun h))

section Input


@[expose] def GGExcAdjOddLayerCores (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (A : Subgroup ↥(adjointGroup τ K)),
    Odd (Nat.card A) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ∃ (β : Type) (T : β → Subgroup ↥(adjointGroup τ K)),
        LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) T

@[expose] def GGE6InndiagOddLayerCores : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (A : Subgroup (MulAut ↥(adjointGroup .E6 K))),
    Odd (Nat.card A) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A ≤ LayerSixE.inndiagAut .E6 K →
      ∃ (β : Type) (T : β → Subgroup ↥(adjointGroup .E6 K)),
        LayerCores.IsSubCoreFamily (LayerSixE.autFix A) T

theorem ggExcAdjLayerCentInvolTrivial_of_oddLayer {τ : Tag} (h : GGExcAdjOddLayerCores τ) :
    GGExcAdjLayerCentInvolTrivial τ := by
  intro K _ _ _ p hp hp2 _ A hA hAc _ _
  haveI := generated_group_finite τ K
  obtain ⟨_, _, hT⟩ := h K A (LayerCores.odd_card_of_isPGroup hp hp2 hA) hAc
  exact LayerCores.layerCentre_of_isSubCoreFamily hT

theorem ggE6InndiagLayerCentInvolTrivial_of_oddLayer (h : GGE6InndiagOddLayerCores) :
    GGE6InndiagLayerCentInvolTrivial := by
  intro K _ _ _ p hp hp2 _ A hA hAc hAi _ _
  haveI := generated_group_finite .E6 K
  haveI := finite_mulAut_oddLayer ↥(adjointGroup .E6 K)
  obtain ⟨_, _, hT⟩ := h K A (LayerCores.odd_card_of_isPGroup hp hp2 hA) hAc hAi
  exact LayerCores.layerCentre_of_isSubCoreFamily hT

end Input

section Bundle


@[expose] def GGTwE6OddLayerCores : Prop :=
  ∀ f : ℕ, 1 ≤ f →
    ∀ A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), Odd (Nat.card A) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      A ≤ LayerSixE.twInndiagAut f →
        ∃ (β : Type) (T : β → Subgroup ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))),
          LayerCores.IsSubCoreFamily (LayerSixE.autFix A) T

@[expose] def GGOddLayerCores : Prop :=
  GGExcAdjOddLayerCores .F4 ∧ GGExcAdjOddLayerCores .E7 ∧ GGExcAdjOddLayerCores .E8 ∧
    GGE6InndiagOddLayerCores ∧ GGTwE6OddLayerCores

theorem ggTwE6LayerCentInvolTrivial_of_oddLayer (h : GGTwE6OddLayerCores) :
    GGTwE6LayerCentInvolTrivial := by
  intro f hf p hp hp2 A hA hAc hAi _ _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := by
    have : Finite (Module.End (GaloisField 2 (2 * f))
      (RootModule TwistTag.E6.tag (GaloisField 2 (2 * f)))) :=
      Module.finite_of_finite (GaloisField 2 (2 * f))
    infer_instance
  haveI := finite_mulAut_oddLayer ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
    (frobQ 2 f))
  obtain ⟨_, _, hT⟩ := h f hf A (LayerCores.odd_card_of_isPGroup hp hp2 hA) hAc hAi
  exact LayerCores.layerCentre_of_isSubCoreFamily hT

theorem ggLayerCentInvolTrivialCores_of_oddLayer (h : GGOddLayerCores) :
    GGLayerCentInvolTrivialCores :=
  ⟨ggExcAdjLayerCentInvolTrivial_of_oddLayer h.1,
    ggExcAdjLayerCentInvolTrivial_of_oddLayer h.2.1,
    ggExcAdjLayerCentInvolTrivial_of_oddLayer h.2.2.1,
    ggE6InndiagLayerCentInvolTrivial_of_oddLayer h.2.2.2.1,
    ggTwE6LayerCentInvolTrivial_of_oddLayer h.2.2.2.2⟩

end Bundle

end CFSG.StandardType
