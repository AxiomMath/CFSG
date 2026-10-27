module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveFam
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.RonanE111Defs
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InFGroup IsOmegaColl genEi)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

@[expose] def fourFiveFAS (j : ℕ) (R : Type) [Group R] [Finite R] : Prop :=
  ∀ (T : Subgroup R) (Ω : Set (Subgroup R)), IsSylowIn 2 T ⊤ → E1.IsInvColl ⊤ Ω → Ω.Nonempty →
    (∀ A ∈ Ω, A ≠ ⊥) →
      ((E1.eGen j ⊤ T Ω : Subgroup R) : Set R) * (T : Set R) = Set.univ

@[expose] def fourFiveCompFAS (j : ℕ) (Q : Type) [Group Q] [Finite Q] (S : Subgroup Q) : Prop :=
  ∀ X : Subgroup Q, X.Normal → X ≠ ⊥ → (∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X) →
    ¬ IsMulCommutative X → ∀ L : Subgroup Q, IsComponentOf L X →
      ∃ h : ((F12.autC S L).subgroupOf (F12.autNL S L)).Normal,
        haveI := h
        fourFiveFAS j (↥(F12.autNL S L) ⧸ (F12.autC S L).subgroupOf (F12.autNL S L))

@[expose] def fourFiveQuotCompFAS (j : ℕ) (Q : Type) [Group Q] [Finite Q] (T : Subgroup Q) :
    Prop :=
  ∀ Y : Subgroup Q, ∀ _ : Y.Normal, fourFiveCompFAS j (Q ⧸ Y) (T.map (QuotientGroup.mk' Y))

private theorem fourFive_eGenP_le_eGen {Q : Type} [Group Q] [Finite Q] (j : ℕ)
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω) :
    F12.eGenP j (⊤ : Subgroup Q) T Ω ≤ E1.eGen j (⊤ : Subgroup Q) T Ω :=
  iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK =>
    le_iSup₂_of_le A hA (le_iSup_of_le hAT
      (le_iSup₂_of_le K (isE_of_isEP hT hAT (hΩ.elemAbelian A hA) hK) le_rfl))

theorem fourFive_genEi_le_eGen {Q : Type} [Group Q] [Finite Q] (j : ℕ) {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω) :
    genEi j T Ω ≤ E1.eGen j ⊤ T Ω :=
  (genEi_le_eGenP j T hΩ).trans (fourFive_eGenP_le_eGen j hT hΩ)

theorem fourFive_fas_of_inFGroup {j : ℕ} {R : Type} [Group R] [Finite R] (h : InFGroup j R) :
    fourFiveFAS j R := by
  intro T Ω hT hΩ hne hbot
  have hΩ' : IsOmegaColl Ω := isOmegaColl_of_isInvColl_top hΩ hne hbot
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  have hF : ((genEi j T Ω : Subgroup R) : Set R) * (T : Set R) = Set.univ := h T hT' Ω hΩ'
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hF]
  exact Set.mul_subset_mul_right
    (SetLike.coe_subset_coe.mpr (fourFive_genEi_le_eGen j hT hΩ'))

theorem fourFive_compFAS_of_inFGroup {j : ℕ} {Q : Type} [Group Q] [Finite Q] {S : Subgroup Q}
    (h : ∀ X : Subgroup Q, X.Normal → X ≠ ⊥ →
      (∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X) → ¬ IsMulCommutative X →
      ∀ L : Subgroup Q, IsComponentOf L X →
        ∃ h : ((F12.autC S L).subgroupOf (F12.autNL S L)).Normal,
          haveI := h
          InFGroup j (↥(F12.autNL S L) ⧸ (F12.autC S L).subgroupOf (F12.autNL S L))) :
    fourFiveCompFAS j Q S := by
  intro X hXn hX hmin hnc L hL
  obtain ⟨hnorm, hF⟩ := h X hXn hX hmin hnc L hL
  exact ⟨hnorm, fourFive_fas_of_inFGroup hF⟩

theorem fourFive_quotCompFAS_of_inFGroup {j : ℕ} {Q : Type} [Group Q] [Finite Q]
    {T : Subgroup Q}
    (h : ∀ Y : Subgroup Q, ∀ _ : Y.Normal,
      ∀ X : Subgroup (Q ⧸ Y), X.Normal → X ≠ ⊥ →
      (∀ N : Subgroup (Q ⧸ Y), N.Normal → N ≤ X → N = ⊥ ∨ N = X) → ¬ IsMulCommutative X →
      ∀ L : Subgroup (Q ⧸ Y), IsComponentOf L X →
        ∃ h : ((F12.autC (T.map (QuotientGroup.mk' Y)) L).subgroupOf
            (F12.autNL (T.map (QuotientGroup.mk' Y)) L)).Normal,
          haveI := h
          InFGroup j (↥(F12.autNL (T.map (QuotientGroup.mk' Y)) L) ⧸
            (F12.autC (T.map (QuotientGroup.mk' Y)) L).subgroupOf
              (F12.autNL (T.map (QuotientGroup.mk' Y)) L))) :
    fourFiveQuotCompFAS j Q T := by
  intro Y hY
  exact fourFive_compFAS_of_inFGroup (h Y hY)

end CFSG.LocalAnalysis.WeakClosure81
