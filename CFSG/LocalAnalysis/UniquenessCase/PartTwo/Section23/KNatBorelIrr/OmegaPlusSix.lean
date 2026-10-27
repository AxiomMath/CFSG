module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitRootData
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O6pLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaPlusSixRoot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.RootTransfer
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryMaxBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Certificate43
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusUnip

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (plusDerivedEquiv plusDerivedUnipotent)
open scoped MatrixGroups

theorem exists_lift_omegaPlusEmb {K : Type} [Field K] {G : Type} [Group G]
    (f : G →* ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)))
    (hf : ∀ g, f g ∈ orthElementaryGroup (quadPlus 3 K)) :
    ∃ ρ : G →* ↥(StatedOmega (StatedQuadPlus 3 K)), ∀ g, omegaPlusEmb K (ρ g) = f g := by
  refine ⟨(plusDerivedEquiv 3 K le_rfl).symm.toMonoidHom.comp
    (f.codRestrict (orthElementaryGroup (quadPlus 3 K)) hf), ?_⟩
  intro g
  change (((plusDerivedEquiv 3 K le_rfl)
    ((plusDerivedEquiv 3 K le_rfl).symm
      (f.codRestrict (orthElementaryGroup (quadPlus 3 K)) hf g))) : PlusLin K) = f g
  simp

theorem normalizer_plusDerivedUnipotent {K : Type} [Field K] [Finite K] [CharP K 2] :
    Subgroup.normalizer (plusDerivedUnipotent 3 K : Set ↥(StatedOmega (StatedQuadPlus 3 K))) =
      (borel 3 K).comap (omegaPlusEmb K) := by
  have h := Subgroup.map_equiv_normalizer_eq ((posUnip 3 K).subgroupOf (splitE K))
    (plusDerivedEquiv 3 K le_rfl).symm
  rw [normalizer_posUnip (K := K) (r := 3) (by norm_num)
      (fun a ha => map_flag_top_ne_Xstar (K := K) (by norm_num) ha),
    map_symm_posUnip_subgroupOf K, flagStab_eq_borel] at h
  rw [← h]
  exact (Subgroup.comap_equiv_eq_map_symm' (plusDerivedEquiv 3 K le_rfl)
    ((borel 3 K).subgroupOf (splitE K))).symm

theorem exists_rootHom_omegaPlusSix {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ ρ : SL(2, K) →* ↥(StatedOmega (StatedQuadPlus 3 K)),
      ρ.range ≤ omegaPlusQAlpha K ∧
      ∀ c : Kˣ, ρ (torusSL c) ∈
          Subgroup.normalizer (plusDerivedUnipotent 3 K : Set ↥(StatedOmega (StatedQuadPlus 3 K))) ∧
        (((ρ (torusSL c) : ↥(StatedOmega (StatedQuadPlus 3 K))) : GL (Fin 3 ⊕ Fin 3) K) :
            Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
            (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) =
          (c : K) • (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) := by
  have hf : ∀ A : SL(2, K), plusRootAlpha K A ∈ orthElementaryGroup (quadPlus 3 K) :=
    fun A => (mem_plusFlagStab.1 (plusRootAlpha_mem A)).1
  obtain ⟨ρ, hρ⟩ := exists_lift_omegaPlusEmb (plusRootAlpha K) hf
  refine ⟨ρ, ?_, ?_⟩
  · rintro x ⟨A, rfl⟩
    exact Subgroup.mem_comap.2 (by rw [hρ A]; exact plusRootAlpha_mem A)
  · intro c
    have htc : omegaPlusEmb K (ρ (torusSL c)) = torusElt 3 K ![c, c⁻¹, 1] := by
      rw [hρ (torusSL c), plusRootAlpha_eq_torusElt c (torusSL c) rfl]
    refine ⟨?_, ?_⟩
    · rw [normalizer_plusDerivedUnipotent, Subgroup.mem_comap, htc]
      exact torusElt_alpha_mem_borel c
    · rw [← omegaPlusEmb_apply (K := K) (ρ (torusSL c)) (Pi.single (Sum.inl 0) 1), htc,
        torusElt_alpha_apply_e0]

theorem hasRootSL2_omegaPlusSix {K : Type} [Field K] [Finite K] [CharP K 2] :
    HasRootSL2 (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl 0) 1) := by
  obtain ⟨U, hU⟩ := exists_sylow_plusDerivedUnipotent K
  obtain ⟨ρ, hρrange, hρtor⟩ := exists_rootHom_omegaPlusSix (K := K)
  obtain ⟨-, -, -, hleast⟩ := leastParabolic_omegaPlusQAlpha K
  refine hasRootSL2_of_leastParabolic (MulEquiv.refl _) U (omegaPlusQAlpha K)
    (omegaPlusQZero K) ρ ?_ ?_ ?_ hρrange ?_
  · have hφ : (MulEquiv.refl ↥(StatedOmega (StatedQuadPlus 3 K))).toMonoidHom =
        MonoidHom.id ↥(StatedOmega (StatedQuadPlus 3 K)) := rfl
    rw [hφ, Subgroup.map_id]
    rfl
  · rw [hU]
    exact plusDerivedUnipotent_le_omegaPlusQZero K
  · intro P hP hUP hnot
    rw [hU] at hUP
    exact hleast P hP hUP hnot
  · intro c
    rw [hU]
    exact hρtor c

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
