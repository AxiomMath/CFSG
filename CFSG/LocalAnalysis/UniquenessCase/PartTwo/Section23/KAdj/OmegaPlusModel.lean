module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusBlocks
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.Open.StatedDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.AGLEmbedding.LeviBlock CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD (lineStab mem_lineStab)
open scoped Matrix
open scoped Pointwise

abbrev PlusLin (K : Type) [Field K] : Type := (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)

@[expose] noncomputable def omegaPlusEmb (K : Type) [Field K] :
    ↥(StatedOmega (StatedQuadPlus 3 K)) →* PlusLin K :=
  (Subgroup.subtype (elementaryGroup (quadPlus 3 K))).comp
    (statedOmegaPlusEquiv (le_rfl : (3 : ℕ) ≤ 3)).toMonoidHom

abbrev omegaPlusQZero (K : Type) [Field K] : Subgroup ↥(StatedOmega (StatedQuadPlus 3 K)) :=
  lineStab (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl ⟨0, by omega⟩) 1)

@[expose] noncomputable def omegaPlusQAlpha (K : Type) [Field K] :
    Subgroup ↥(StatedOmega (StatedQuadPlus 3 K)) :=
  (plusFlagStab K 3 ({2, 3} : Finset ℕ)).comap (omegaPlusEmb K)

private lemma flag_three_one_eq_span_singleton_E02 {K : Type} [Field K] :
    flag 3 K 1 = Submodule.span K {Pi.single (Sum.inl (0 : Fin 3)) (1 : K)} := by
  have hset : (fun j : Fin 3 =>
        (Pi.single (Sum.inl j) (1 : K) : Fin 3 ⊕ Fin 3 → K)) '' {j | (j : ℕ) < 1}
      = {Pi.single (Sum.inl (0 : Fin 3)) (1 : K)} := by
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjval : (j : ℕ) = 0 := Nat.lt_one_iff.mp hj
      have hj0 : j = 0 := Fin.ext (by simpa using hjval)
      subst hj0
      rfl
    · intro hv
      exact ⟨0, by simp, hv.symm⟩
  rw [flag, hset]

private lemma e1_E02_ne_zero {K : Type} [Field K] :
    (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    simpa using congrFun h (Sum.inl (0 : Fin 3))
  exact one_ne_zero h1

private lemma mem_span_singleton_map_iff_E02 {K V : Type} [Field K] [AddCommGroup V]
    [Module K V]
    (g : V ≃ₗ[K] V) {v : V} (hv : v ≠ 0) :
    (Submodule.span K {v}).map (g : V →ₗ[K] V) = Submodule.span K {v} ↔
      ∃ c : K, g v = c • v := by
  constructor
  · intro h
    have hmem : g v ∈ Submodule.span K {v} := by
      rw [← h]
      exact Submodule.mem_map.mpr ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact hv (g.injective (by rw [hc, map_zero]))
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span K {g v} = Submodule.span K {v}
    rw [hc]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0) v

private lemma map_lineStab_le_plusFlagStab_E02 {K : Type} [Field K]
    {w : Fin 3 ⊕ Fin 3 → K} (hw : w ≠ 0)
    (hflag : flag 3 K 1 = Submodule.span K {w}) :
    (lineStab (StatedOmega (StatedQuadPlus 3 K)) w).map (omegaPlusEmb K) ≤
      plusFlagStab K 3 ({1} : Finset ℕ) := by
  intro g hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨A, hA, rfl⟩ := hg
  rw [mem_plusFlagStab]
  refine ⟨(statedOmegaPlusEquiv (le_rfl : (3 : ℕ) ≤ 3) A).2, ?_⟩
  intro d hd
  obtain rfl := Finset.mem_singleton.mp hd
  obtain ⟨c, hc⟩ := mem_lineStab.mp hA
  have hc' : (omegaPlusEmb K A) w = c • w := by
    rw [show (omegaPlusEmb K A) w =
          (A : GL (Fin 3 ⊕ Fin 3) K).val *ᵥ w from
        statedOmegaPlusEquiv_app (le_rfl : (3 : ℕ) ≤ 3) A w]
    exact hc
  have hmap : (Submodule.span K {w}).map
        (omegaPlusEmb K A :
          (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) =
        Submodule.span K {w} :=
    (mem_span_singleton_map_iff_E02 (omegaPlusEmb K A) hw).mpr ⟨c, hc'⟩
  rw [hflag, ← MulAction.mem_stabilizer_iff,
    Submodule.mem_stabilizer_submodule_iff_map_eq]
  exact hmap

private lemma plusFlagStab_le_map_lineStab_E02 {K : Type} [Field K]
    {w : Fin 3 ⊕ Fin 3 → K} (hw : w ≠ 0)
    (hflag : flag 3 K 1 = Submodule.span K {w}) :
    plusFlagStab K 3 ({1} : Finset ℕ) ≤
      (lineStab (StatedOmega (StatedQuadPlus 3 K)) w).map (omegaPlusEmb K) := by
  intro g hg
  have hg' := mem_plusFlagStab.mp hg
  let g' : Gom (quadPlus 3 K) := ⟨g, hg'.1⟩
  rw [Subgroup.mem_map]
  refine ⟨(statedOmegaPlusEquiv (le_rfl : (3 : ℕ) ≤ 3)).symm g', ?_, ?_⟩
  · rw [mem_lineStab]
    have hstab : g • flag 3 K 1 = flag 3 K 1 := hg'.2 1 (by simp)
    have hmap : (flag 3 K 1).map
          (g : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) = flag 3 K 1 := by
      rw [← MulAction.mem_stabilizer_iff,
        Submodule.mem_stabilizer_submodule_iff_map_eq] at hstab
      exact hstab
    rw [hflag] at hmap
    obtain ⟨c, hc⟩ := (mem_span_singleton_map_iff_E02 g hw).mp hmap
    have hAw : ((((statedOmegaPlusEquiv (le_rfl : (3 : ℕ) ≤ 3)).symm g' :
        GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) *ᵥ w =
        g'.app w :=
      statedOmegaPlusEquiv_symm_app (le_rfl : (3 : ℕ) ≤ 3) g' w
    exact ⟨c, hAw.trans hc⟩
  · change ((statedOmegaPlusEquiv (le_rfl : (3 : ℕ) ≤ 3))
          ((statedOmegaPlusEquiv (le_rfl : (3 : ℕ) ≤ 3)).symm g') :
        (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) = g
    rw [MulEquiv.apply_symm_apply]

theorem omegaPlusEmb_injective (K : Type) [Field K] : Function.Injective (omegaPlusEmb K) := by
  intro A B hAB
  exact (statedOmegaPlusEquiv (le_rfl : (3 : ℕ) ≤ 3)).injective (Subtype.val_injective hAB)

theorem omegaPlusEmb_apply {K : Type} [Field K] (A : ↥(StatedOmega (StatedQuadPlus 3 K)))
    (v : Fin 3 ⊕ Fin 3 → K) : omegaPlusEmb K A v = (A : GL (Fin 3 ⊕ Fin 3) K).val *ᵥ v := by
  exact statedOmegaPlusEquiv_app (le_rfl : (3 : ℕ) ≤ 3) A v

theorem map_omegaPlusQZero (K : Type) [Field K] :
    (omegaPlusQZero K).map (omegaPlusEmb K) = plusFlagStab K 3 ({1} : Finset ℕ) := by
  refine le_antisymm ?_ ?_
  · exact map_lineStab_le_plusFlagStab_E02 e1_E02_ne_zero flag_three_one_eq_span_singleton_E02
  · exact plusFlagStab_le_map_lineStab_E02 e1_E02_ne_zero flag_three_one_eq_span_singleton_E02

theorem map_omegaPlusQAlpha_le (K : Type) [Field K] :
    (omegaPlusQAlpha K).map (omegaPlusEmb K) ≤ plusFlagStab K 3 ({2, 3} : Finset ℕ) :=
  (Subgroup.map_comap_le _ _)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
