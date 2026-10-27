module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusVectors
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.RootGroupGL
import CFSG.ClassicalGroups.Orthogonal.RootGroupGLEichler
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Pow3OmegaMinus
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
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

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL lineStabilizer mem_lineStabilizer_iff
  conj_mem_rootGroupGL)
open CFSG.GroupTheory.WeirSylow (statedOmega_le_isometryCore apply_mulVec_of_mem_isometryCore)
open CFSG.LieType.Universal.Spin (quadMinus)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

theorem rootGroupGL_le_statedOmega_minus [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (u : ιM → K) :
    rootGroupGL (quadMinus 2 K b c) u ≤ StatedOmega (StatedQuadMinus 2 K b c) := fun _ hA =>
  (CFSG.ClassicalGroups.Orthogonal.mem_statedOmega_iff_mem_elementaryGroup
      (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le le_rfl
        hirr)).mpr
    (CFSG.ClassicalGroups.Orthogonal.rootGroup_le_elementaryGroup _ u hA)

private theorem isometry_of_mem_statedOmega_minus {b c : K} {g : GL ιM K}
    (hg : g ∈ StatedOmega (StatedQuadMinus 2 K b c)) :
    ∀ v, quadMinus 2 K b c ((g : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v := by
  intro v
  have h := apply_mulVec_of_mem_isometryCore
    (Q₀ := StatedQuadMinus 2 K b c) (statedOmega_le_isometryCore _ hg) v
  rwa [← CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c] at h

private theorem card_rootGroupGL_e1M [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) = Nat.card K ^ 2 := by
  rw [card_rootGroupGL (Q := quadMinus 2 K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n := 2) (K := K)
      hirr) (quadMinus_e1M b c) e1M_ne_zero]
  have hc : Fintype.card ιM = 4 := by simp [Fintype.card_sum]
  rw [hc]

private theorem isPGroup_rootGroupGL_e1M [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsPGroup 2 ↥(rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) :=
  isPGroup_rootGroupGL
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n := 2) (K := K)
      hirr) (quadMinus_e1M b c) e1M_ne_zero

private theorem odd_pow_four_sub_one {q : ℕ} (hq : Even q) (hq0 : 0 < q) :
    Odd (q ^ 4 - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow 4 q hq0) (Even.pow_of_ne_zero (n := 4) hq (by norm_num))
    (by norm_num)

theorem le_rootGroupGL_of_le_statedOmega [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {P : Subgroup (GL ιM K)}
    (hPΩ : P ≤ StatedOmega (StatedQuadMinus 2 K b c))
    (hPfix : ∀ g ∈ P, (g : Matrix ιM ιM K) *ᵥ KTabC.e1M K = KTabC.e1M K)
    (hP2 : IsPGroup 2 ↥P) :
    P ≤ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set U : Subgroup (GL ιM K) := rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) with hU
  have hline : ∀ g ∈ P, g ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K) := by
    intro g hg
    exact (mem_lineStabilizer_iff (quadMinus 2 K b c)).mpr
      ⟨isometry_of_mem_statedOmega_minus (hPΩ hg), 1, by rw [hPfix g hg, one_smul]⟩
  have hnorm : P ≤ Subgroup.normalizer U := by
    intro g hg
    have hgL := hline g hg
    have hgiL : g⁻¹ ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K) :=
      (lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)).inv_mem hgL
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [hU] at hu ⊢
      exact conj_mem_rootGroupGL hgL hu
    · intro hu
      rw [hU] at hu ⊢
      have h := conj_mem_rootGroupGL hgiL hu
      have hcancel : g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ = u := by group
      rwa [hcancel] at h
  have hSU2 : IsPGroup 2 ↥(P ⊔ U) :=
    IsPGroup.to_sup_of_normal_right' hP2 (by rw [hU]; exact isPGroup_rootGroupGL_e1M hirr) hnorm
  have hSUΩ : P ⊔ U ≤ StatedOmega (StatedQuadMinus 2 K b c) :=
    sup_le hPΩ (by simpa only [hU] using rootGroupGL_le_statedOmega_minus hirr (KTabC.e1M K))
  have hSUdvd : Nat.card ↥(P ⊔ U) ∣ Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    have h := Subgroup.card_dvd_of_le hSUΩ
    rwa [CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.card_statedOmega_quadMinus_two_eq
      (K := K) (b := b) (c := c) hirr] at h
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  have hq0 : 0 < Nat.card K := by rw [hq]; positivity
  have heven : Even (Nat.card K) := by
    rw [hq]
    exact Even.pow_of_ne_zero (n := (m : ℕ)) (by norm_num) m.pos.ne'
  have hodd : Odd (Nat.card K ^ 4 - 1) := odd_pow_four_sub_one heven hq0
  obtain ⟨t, ht⟩ := hSU2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥(P ⊔ U)) (Nat.card K ^ 4 - 1) := by
    rw [ht]
    exact Nat.Coprime.pow_left t (Odd.coprime_two_left hodd)
  have hSUle : Nat.card ↥(P ⊔ U) ≤ Nat.card K ^ 2 :=
    Nat.le_of_dvd (pow_pos hq0 2) (Nat.Coprime.dvd_of_dvd_mul_right hcop hSUdvd)
  have hUcard : Nat.card ↥U = Nat.card K ^ 2 := by
    rw [hU]
    exact card_rootGroupGL_e1M hirr
  have heq : U = P ⊔ U :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hUcard]; exact hSUle)
  intro g hg
  have hg' : g ∈ P ⊔ U := Subgroup.mem_sup_left hg
  rwa [← heq] at hg'

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
