module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Fixed
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusSylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.RootGroupGL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.ClassicalGroups.Orthogonal.RootGroupGLEichler
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
import CFSG.ClassicalGroups.Orthogonal.MinusSplitTorus
import Mathlib.FieldTheory.Finite.Basic
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRankOddMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open Matrix
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL lineStabilizer mem_lineStabilizer_iff
  conj_mem_rootGroupGL)
open CFSG.LieType.Universal.Spin (quadMinus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem isometry_of_mem_statedOmega_minus_L21 {b c : K} {g : GL ιM K}
    (hg : g ∈ StatedOmega (StatedQuadMinus 2 K b c)) :
    ∀ v, quadMinus 2 K b c ((g : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v := by
  intro v
  have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
    (Q₀ := StatedQuadMinus 2 K b c)
    (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore _ hg) v
  rwa [← CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c] at h

private theorem mem_lineStabilizer_of_mem_lineStab_L21 {b c : K}
    {g : ↥(StatedOmega (StatedQuadMinus 2 K b c))}
    (hg : g ∈ KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K)) :
    (g : GL ιM K) ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K) := by
  obtain ⟨d, hd⟩ := KTabD.mem_lineStab.mp hg
  exact (mem_lineStabilizer_iff (quadMinus 2 K b c)).mpr
    ⟨isometry_of_mem_statedOmega_minus_L21 g.2, d, hd⟩

private theorem conj_mem_rootGroupGL_subgroupOf_L21 {b c : K}
    {g : ↥(StatedOmega (StatedQuadMinus 2 K b c))}
    (hg : g ∈ KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K))
    {h : ↥(StatedOmega (StatedQuadMinus 2 K b c))}
    (hh : h ∈ (rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)).subgroupOf
      (StatedOmega (StatedQuadMinus 2 K b c))) :
    g * h * g⁻¹ ∈ (rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)).subgroupOf
      (StatedOmega (StatedQuadMinus 2 K b c)) := by
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  have hconj := conj_mem_rootGroupGL (mem_lineStabilizer_of_mem_lineStab_L21 hg) hh
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj

theorem sylow_eq_rootGroupGL_omegaMinusFour (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 K b c)))
    (hU : (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤
      KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K)) :
    (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) =
      (rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)).subgroupOf
        (StatedOmega (StatedQuadMinus 2 K b c)) := by
  classical
  set R : Subgroup (GL ιM K) := rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) with hR
  let P : Subgroup (GL ιM K) :=
    (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))).map
      (StatedOmega (StatedQuadMinus 2 K b c)).subtype
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
    (n := 2) (K := K) hirr
  have hPΩ : P ≤ StatedOmega (StatedQuadMinus 2 K b c) := Subgroup.map_subtype_le _
  have hPfix : ∀ g ∈ P, (g : Matrix ιM ιM K) *ᵥ KTabC.e1M K = KTabC.e1M K := by
    rintro g ⟨u, hu, rfl⟩
    exact mulVec_eq_of_mem_sylow_le_lineStab KOm.e1M_ne_zero U hU hu
  have hP2 : IsPGroup 2 ↥P := U.isPGroup'.map (StatedOmega (StatedQuadMinus 2 K b c)).subtype
  have hPR : P ≤ R := KOm.le_rootGroupGL_of_le_statedOmega hirr hPΩ hPfix hP2
  have hUR : (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤
      R.subgroupOf (StatedOmega (StatedQuadMinus 2 K b c)) := by
    intro u hu
    rw [Subgroup.mem_subgroupOf]
    exact hPR (Subgroup.mem_map_of_mem (StatedOmega (StatedQuadMinus 2 K b c)).subtype hu)
  have hR2 : IsPGroup 2 ↥(R.subgroupOf (StatedOmega (StatedQuadMinus 2 K b c))) :=
    (KOm.isPGroup_rootGroupGL hQ (KOm.quadMinus_e1M b c) KOm.e1M_ne_zero).comap_subtype
  exact (U.is_maximal' hR2 hUR).symm

theorem normalizer_le_lineStab_omegaMinusFour (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 K b c)))
    (hU : (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤
      KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K)) :
    Subgroup.normalizer ((U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
        Set ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤
      KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K) := by
  classical
  intro g hg
  rw [KTabD.mem_lineStab]
  have hfix : ∀ s ∈ (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))),
      ((s : GL ιM K) : Matrix ιM ιM K) *ᵥ
        (((g : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K) =
      ((g : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K := by
    intro s hs
    have hconj : g⁻¹ * s * g ∈ (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) :=
      (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
    have hfix1 := mulVec_eq_of_mem_sylow_le_lineStab KOm.e1M_ne_zero U hU hconj
    calc
      ((s : GL ιM K) : Matrix ιM ιM K) *ᵥ
          (((g : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K)
          = (((s * g : ↥(StatedOmega (StatedQuadMinus 2 K b c))) : GL ιM K) :
              Matrix ιM ιM K) *ᵥ KTabC.e1M K := by
              rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]
      _ = (((g * (g⁻¹ * s * g) : ↥(StatedOmega (StatedQuadMinus 2 K b c))) : GL ιM K) :
              Matrix ιM ιM K) *ᵥ KTabC.e1M K := by
              rw [show s * g = g * (g⁻¹ * s * g) from by group]
      _ = ((g : GL ιM K) : Matrix ιM ιM K) *ᵥ
            ((((g⁻¹ * s * g : ↥(StatedOmega (StatedQuadMinus 2 K b c))) : GL ιM K) :
              Matrix ιM ιM K) *ᵥ KTabC.e1M K) := by
              rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]
      _ = ((g : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K := by rw [hfix1]
  exact (fixed_iff_of_sylow_le_lineStab KOm.e1M_ne_zero
    (KTabC.sylowFixedLine_minus K b c hirr) U hU
    (((g : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K)).mp hfix

theorem lineStab_le_normalizer_omegaMinusFour (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 K b c)))
    (hU : (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤
      KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K)) :
    KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K) ≤
      Subgroup.normalizer ((U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
        Set ↥(StatedOmega (StatedQuadMinus 2 K b c))) := by
  classical
  rw [sylow_eq_rootGroupGL_omegaMinusFour hirr U hU]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_rootGroupGL_subgroupOf_L21 hg hh
  · intro hh
    have h1 := conj_mem_rootGroupGL_subgroupOf_L21
      ((KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K)).inv_mem hg) hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h from by group] at h1

theorem exists_mulVec_e1M_eq_smul_omegaMinusFour (a : Kˣ) :
    ∃ t : ↥(StatedOmega (StatedQuadMinus 2 K b c)),
      ((t : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ
        KTabC.e1M K = (a : K) • KTabC.e1M K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (m : ℕ) := Nat.card_eq_fintype_card.trans hm
  have hOdd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units K, hcard]
    exact Nat.Even.sub_odd (one_le_pow₀ (show (1 : ℕ) ≤ 2 by norm_num))
      (Even.pow_of_ne_zero even_two (n := (m : ℕ)) m.ne_zero) odd_one
  refine ⟨CFSG.ClassicalGroups.Orthogonal.minusDiagGL (b := b) (c := c) (n := 2) hOdd
    (fun _ => a) (fun _ => ?_), ?_⟩
  · exact pow_card_eq_one'
  · rw [CFSG.ClassicalGroups.Orthogonal.coe_minusDiagGL]
    rw [CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.mulVec_diagGL]
    funext j
    rcases j with j | j | j
    · have hj : j = 0 := Fin.eq_zero j
      rw [hj]
      simp [KTabC.e1M,
        CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.torusEntMinus]
    · have hj : j = 0 := Fin.eq_zero j
      rw [hj]
      simp [KTabC.e1M,
        CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.torusEntMinus]
    · simp [KTabC.e1M,
        CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.torusEntMinus]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

end
