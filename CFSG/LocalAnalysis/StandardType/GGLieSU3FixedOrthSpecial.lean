module

public import CFSG.Assembly.Defs
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet

import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock
import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerCore
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourNorm
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Polynomial CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary

open scoped commutatorElement

theorem ggLieSU3Fixed_eq_specialBlock {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) {j : K[X]}
    (hj : j ∈ primaryFactors y.toLinearMap) (hj1 : j ≠ X - 1) {D : Subgroup (V ≃ₗ[K] V)}
    (hDsub : CFSG.Assembly.IsSubnormal D ⁅supportedBlock Q y j, supportedBlock Q y j⁆)
    (hDq : CFSG.Assembly.IsQuasisimple ↥D) :
    D = specialBlock Q y j ∧ 2 ≤ primaryMultiplicity y.toLinearMap j := by
  classical
  haveI : Fact (Irreducible j) := ⟨irreducible_of_mem_primaryFactors hj⟩
  have hcomm_le : ⁅supportedBlock Q y j, supportedBlock Q y j⁆ ≤ specialBlock Q y j := by
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    have hmem : ⁅g, g'⁆ ∈ supportedBlock Q y j := by
      rw [commutatorElement_def]
      exact (supportedBlock Q y j).mul_mem
        ((supportedBlock Q y j).mul_mem
          ((supportedBlock Q y j).mul_mem hg hg') ((supportedBlock Q y j).inv_mem hg))
        ((supportedBlock Q y j).inv_mem hg')
    refine mem_specialBlock.mpr ⟨hmem, ?_⟩
    let u : ↥(supportedBlock Q y j) := ⟨g, hg⟩
    let v : ↥(supportedBlock Q y j) := ⟨g', hg'⟩
    have huv : (⟨⁅g, g'⁆, hmem⟩ : ↥(supportedBlock Q y j)) = ⁅u, v⁆ := Subtype.ext rfl
    rw [huv, commutatorElement_def, map_mul, map_mul, map_mul]
    have hd : blockDet Q y j u * blockDet Q y j u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hd' : blockDet Q y j v * blockDet Q y j v⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    calc blockDet Q y j u * blockDet Q y j v * blockDet Q y j u⁻¹ * blockDet Q y j v⁻¹
        = (blockDet Q y j u * blockDet Q y j u⁻¹) *
          (blockDet Q y j v * blockDet Q y j v⁻¹) := by ac_rfl
      _ = 1 := by rw [hd, hd', mul_one]
  have hFB : specialBlock Q y j ≤ supportedBlock Q y j := specialBlock_le_supportedBlock j
  have hBnorm : (⁅supportedBlock Q y j, supportedBlock Q y j⁆.subgroupOf
      (supportedBlock Q y j)).Normal := by
    have h := Subgroup.normal_subgroupOf_commutator_sup
      (H₁ := supportedBlock Q y j) (H₂ := supportedBlock Q y j)
    rwa [sup_idem] at h
  have hNB : CFSG.Assembly.IsSubnormal ⁅supportedBlock Q y j, supportedBlock Q y j⁆
      (supportedBlock Q y j) :=
    CFSG.Assembly.IsSubnormal.step (Subgroup.commutator_le_self _) hBnorm
      (CFSG.Assembly.IsSubnormal.refl _)
  have hNF : CFSG.Assembly.IsSubnormal ⁅supportedBlock Q y j, supportedBlock Q y j⁆
      (specialBlock Q y j) := by
    have h := hNB.inf_of_le hFB
    rwa [inf_eq_left.mpr hcomm_le] at h
  have hDsub_F : CFSG.Assembly.IsSubnormal D (specialBlock Q y j) := hDsub.trans hNF
  have hDF : D ≤ specialBlock Q y j := hDsub_F.le
  have hDnat : CFSG.IsQuasisimple ↥D :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥D).mp hDq
  have hDnt : Nontrivial ↥D := by
    haveI : IsSimpleGroup (↥D ⧸ Subgroup.center ↥D) := hDq.2
    exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥D))
  have hDnoncomm : ¬ IsMulCommutative ↥D := by
    haveI : Group.IsPerfect ↥D := ⟨hDq.1⟩
    haveI : Nontrivial ↥D := hDnt
    exact Group.IsPerfect.not_isMulCommutative (G := ↥D)
  have hm2 : 2 ≤ primaryMultiplicity y.toLinearMap j := by
    have hmpos : 0 < primaryMultiplicity y.toLinearMap j := by
      have hne := primaryComponent_ne_bot hy.squarefree_minpoly hj
      have : Nontrivial (primaryComponent y.toLinearMap j) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      exact Module.finrank_pos
    rcases Nat.lt_or_ge (primaryMultiplicity y.toLinearMap j) 2 with hlt | hge
    · have hm1 : primaryMultiplicity y.toLinearMap j = 1 := by omega
      have hFbot : specialBlock Q y j = ⊥ :=
        hy.specialBlock_eq_bot_of_finrank_eq_one hj hm1
      have hDbot : D = ⊥ := le_bot_iff.mp (hDF.trans (le_of_eq hFbot))
      haveI : Subsingleton ↥D := by rw [hDbot]; infer_instance
      obtain ⟨a, b, hab⟩ := hDnt
      exact absurd (Subsingleton.elim a b) hab
    · exact hge
  refine ⟨?_, hm2⟩
  rcases SevOm.isQuasisimple_or_isSolvable_specialBlock hy Nat.prime_three (by norm_num) hj hj1
      hm2 with hFq | hFsolv
  · rcases LayerCyc.le_or_commute_of_isSubnormal hDsub_F hFq with hFD | hcomm
    · exact le_antisymm hDF hFD
    · exfalso
      apply hDnoncomm
      refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
      exact hcomm (a : V ≃ₗ[K] V) a.2 (b : V ≃ₗ[K] V) (hDF b.2)
  · exfalso
    haveI : Group.IsSolvable ↥(specialBlock Q y j) := hFsolv
    have hDsolv : Group.IsSolvable ↥D :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hDF)
        (Subgroup.inclusion_injective hDF)
    exact SmallOrthUn.not_isSolvable_of_isQuasisimple hDnat hDsolv

end CFSG.StandardType
