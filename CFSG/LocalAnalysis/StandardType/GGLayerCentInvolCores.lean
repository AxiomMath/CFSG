module

public import CFSG.LocalAnalysis.StandardType.GGLayerChevAdjoint
public import CFSG.LocalAnalysis.StandardType.GGTwE6LayerCentConverse
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowLayer
public import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.GLTheoremA

section Input


@[expose] def GGExcAdjLayerCentInvolTrivial (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    (¬ p ∣ Nat.card K - 1 ∨ p < excWeylBound τ) →
    ∀ A : Subgroup ↥(adjointGroup τ K), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ¬ GGExcToral τ K A → ¬ GGExcHighNonsplit τ K A →
        ∀ z ∈ CFSG.Open.GLALayer (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))),
          (∀ y ∈ CFSG.Open.GLALayer (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))),
            z * y = y * z) → z ^ 2 = 1 → z = 1

@[expose] def GGE6InndiagLayerCentInvolTrivial : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    (¬ p ∣ Nat.card K - 1 ∨ p < 7) →
    ∀ A : Subgroup (MulAut ↥(adjointGroup .E6 K)), IsPGroup p A →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A ≤ LayerSixE.inndiagAut .E6 K →
        ¬ LayerSixE.GGInndiagToral .E6 K A → ¬ GGE6InndiagHighNonsplit K A →
          ∀ z ∈ CFSG.Open.GLALayer (LayerSixE.autFix A),
            (∀ y ∈ CFSG.Open.GLALayer (LayerSixE.autFix A), z * y = y * z) → z ^ 2 = 1 → z = 1

end Input

section Bundle


@[expose] def GGLayerCentInvolTrivialCores : Prop :=
  GGExcAdjLayerCentInvolTrivial .F4 ∧ GGExcAdjLayerCentInvolTrivial .E7 ∧
    GGExcAdjLayerCentInvolTrivial .E8 ∧ GGE6InndiagLayerCentInvolTrivial ∧
      GGTwE6LayerCentInvolTrivial

end Bundle

section Equivalence


private theorem finite_adjointGroup_aux (τ : Tag) (K : Type) [Field K] [Finite K] :
    Finite ↥(adjointGroup τ K) := by
  have : Finite (Module.End K (RootModule τ K)) :=
    Module.finite_of_finite K
  infer_instance

theorem ggExcAdjCoreNonToralSylowRestInput_iff_layerCentre {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    GGExcAdjCoreNonToralSylowRestInput τ ↔ GGExcAdjLayerCentInvolTrivial τ := by
  constructor
  · intro h K _ _ _ p hp hp2 hpK A hA hAc hnT hnH z hz hzc hz2
    obtain ⟨β, T, hT⟩ := h K p hp hp2 hpK A hA hAc hnT hnH
    exact LayerCores.layerCentre_of_isSubCoreFamily hT z hz hzc hz2
  · intro h K _ _ _ p hp hp2 hpK A hA hAc hnT hnH
    haveI := finite_adjointGroup_aux τ K
    obtain ⟨hS, hnc⟩ := LayerCores.adjointGroup_isSimple_nonabelian hτ K
    have hE := LayerCores.centFix_map_conj A
    have key := (LayerCores.exists_subCoreFamily_iff_layerCentre hS hnc
      (LayerCores.isChevSimple_adjointGroup_charTwo hτ K) hp hp2 (A.map MulAut.conj)
      (LayerCores.isPGroup_map_conj hA) (LayerCores.comm_map_conj hAc)).2
      (by rw [hE]; exact h K p hp hp2 hpK A hA hAc hnT hnH)
    rw [hE] at key
    exact key

theorem ggE6InndiagCoreNonToralSylowRestInput_iff_layerCentre :
    GGE6InndiagCoreNonToralSylowRestInput ↔ GGE6InndiagLayerCentInvolTrivial := by
  constructor
  · intro h K _ _ _ p hp hp2 hpK A hA hAc hAD hnT hnH z hz hzc hz2
    obtain ⟨β, T, hT⟩ := h K p hp hp2 hpK A hA hAc hAD hnT hnH
    exact LayerCores.layerCentre_of_isSubCoreFamily hT z hz hzc hz2
  · intro h K _ _ _ p hp hp2 hpK A hA hAc hAD hnT hnH
    haveI := finite_adjointGroup_aux .E6 K
    obtain ⟨hS, hnc⟩ := LayerCores.adjointGroup_isSimple_nonabelian (Or.inr (Or.inl rfl)) K
    have hEq : LayerSixE.autFix A = I142.centFix A :=
      Subgroup.ext fun x => LayerSixE.mem_autFix.trans I142.mem_centFix.symm
    have key := (LayerCores.exists_subCoreFamily_iff_layerCentre hS hnc
      (LayerCores.isChevSimple_adjointGroup_charTwo (Or.inr (Or.inl rfl)) K) hp hp2 A hA hAc).2
      (by rw [← hEq]; exact h K p hp hp2 hpK A hA hAc hAD hnT hnH)
    rw [← hEq] at key
    exact key

theorem ggLayerTagsPilotRestSixSylowCores_iff_layerCentre :
    GGLayerTagsPilotRestSixSylowCores ↔ GGLayerCentInvolTrivialCores :=
  ⟨fun h => ⟨(ggExcAdjCoreNonToralSylowRestInput_iff_layerCentre (Or.inl rfl)).1 h.1,
      (ggExcAdjCoreNonToralSylowRestInput_iff_layerCentre (Or.inr (Or.inr (Or.inl rfl)))).1 h.2.1,
      (ggExcAdjCoreNonToralSylowRestInput_iff_layerCentre (Or.inr (Or.inr (Or.inr rfl)))).1
        h.2.2.1,
      ggE6InndiagCoreNonToralSylowRestInput_iff_layerCentre.1 h.2.2.2.1,
      ggTwE6InndiagCoreRestInput_iff_layerCentre.1 h.2.2.2.2⟩,
    fun h => ⟨(ggExcAdjCoreNonToralSylowRestInput_iff_layerCentre (Or.inl rfl)).2 h.1,
      (ggExcAdjCoreNonToralSylowRestInput_iff_layerCentre (Or.inr (Or.inr (Or.inl rfl)))).2 h.2.1,
      (ggExcAdjCoreNonToralSylowRestInput_iff_layerCentre (Or.inr (Or.inr (Or.inr rfl)))).2
        h.2.2.1,
      ggE6InndiagCoreNonToralSylowRestInput_iff_layerCentre.2 h.2.2.2.1,
      ggTwE6InndiagCoreRestInput_iff_layerCentre.2 h.2.2.2.2⟩⟩

end Equivalence

end CFSG.StandardType
