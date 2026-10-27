module

public import CFSG.LocalAnalysis.StandardType.GGLieOddCoverDefs
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassicalFour
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.LieOddCover

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem exists_ggU_central_cover_of_lieModel
    {t : StatedLieTag} {n f : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 f) {X : Type} [Group X]
    (hX : LieModel X t n 2 f) :
    ∃ q : (ggU t n f).K →* X, Function.Surjective q ∧ q.ker ≤ Subgroup.center (ggU t n f).K := by
  have hFT : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [CFSG.ClassicalInvolution.Generic.IsFundTag]
  have hY : LieModel ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) t n 2 f := by
    have h := (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n 2 f Nat.prime_two hFT hadm).2
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact h
  obtain ⟨e⟩ : Nonempty (((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) ≃* X) := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique_four (Or.inl rfl)
        (hY.statedClassicalModel (by simp [classicalTags]))
        (hX.statedClassicalModel (by simp [classicalTags]))
    ·
      exact CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique_four (Or.inr (Or.inl rfl))
        (hY.statedClassicalModel (by simp [classicalTags]))
        (hX.statedClassicalModel (by simp [classicalTags]))
    ·
      exact CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique_four
        (Or.inr (Or.inr (Or.inl rfl)))
        (hY.statedClassicalModel (by simp [classicalTags]))
        (hX.statedClassicalModel (by simp [classicalTags]))
    ·
      exact CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique_four
        (Or.inr (Or.inr (Or.inr rfl)))
        (hY.statedClassicalModel (by simp [classicalTags]))
        (hX.statedClassicalModel (by simp [classicalTags]))
    ·
      obtain ⟨-, K₁, _, _, hc₁, b₁, c₁, hirr₁, ⟨e₁⟩⟩ :=
        hY.statedClassicalModel (by simp [classicalTags])
      obtain ⟨-, K₂, _, _, hc₂, b₂, c₂, hirr₂, ⟨e₂⟩⟩ :=
        hX.statedClassicalModel (by simp [classicalTags])
      have hn : 1 ≤ n := by have := hadm.2.2; omega
      let φ := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hc₁.trans hc₂.symm)
      obtain ⟨e₃⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (K := K₂) hn
        (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr₁) hirr₂
      exact ⟨e₁.trans (((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
          (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ rfl rfl))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans e₃).trans e₂.symm)⟩
    ·
      exact CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_unique
        (hY.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
        (hX.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
    ·
      exact CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_unique
        (hY.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
        (hX.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
    ·
      exact CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_unique
        (hY.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
        (hX.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
    ·
      exact CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_unique
        (hY.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
        (hX.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
    ·
      exact CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_unique
        (hY.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
        (hX.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (ggU t n f).K)), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro k hk
    have h1 : e (QuotientGroup.mk' (Subgroup.center (ggU t n f).K) k) = 1 := hk
    rw [map_eq_one_iff _ e.injective] at h1
    exact (QuotientGroup.eq_one_iff k).1 h1

end CFSG.StandardType.LieOddCover
