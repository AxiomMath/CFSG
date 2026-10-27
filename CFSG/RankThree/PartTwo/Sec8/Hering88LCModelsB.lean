module

public import CFSG.RankThree.PartTwo.Sec8.Hering88LCModels
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4Conj
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp48Inner
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Ree

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.RankThreeEven (projSp)
open Matrix
open scoped MatrixGroups

section General

variable {M N : Type*} [Group M] [Group N]

structure PerfFacts (Q : Type*) [Group Q] : Prop where
  center : ∀ z : Q, (∀ y : Q, z * y = y * z) → z = 1
  perf : ∀ g : Q, g ^ 3 = 1 → g ≠ 1 → Subgroup.centralizer ({g} : Set Q) ≤
    inSubgroup perfectResidual (Subgroup.centralizer ({g} : Set Q))

theorem PerfFacts.of_mulEquiv (e : M ≃* N) (h : PerfFacts N) : PerfFacts M where
  center z hz := by
    have : e z = 1 := h.center (e z) fun y => by
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hz y]
    exact e.injective (this.trans (map_one e).symm)
  perf g hg3 hg1 p hp := by
    have hpe : e p ∈ Subgroup.centralizer ({e g} : Set N) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hp]
    have h1 := h.perf (e g) (by rw [← map_pow, hg3, map_one])
      (fun h1 => hg1 (e.injective (h1.trans (map_one e).symm))) hpe
    rw [← residual_centralizer_map e g] at h1
    obtain ⟨r, hr, hre⟩ := h1
    rwa [e.injective hre] at hr

end General

section Sp4

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem three_ne_zero_of_charTwo : (3 : F) ≠ 0 := by
  have h31 : (3 : F) = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h2
  rw [h31]
  exact one_ne_zero

theorem isPerfect_sl2 (hF : 4 ≤ Nat.card F) : Group.IsPerfect SL(2, F) := by
  classical
  apply CFSG.LinearGroups.special_linear_dimension_two_perfect
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
  exact ⟨s, hs⟩

theorem commutator_range_eq {H M : Type*} [Group H] [Group M] [Group.IsPerfect H] (f : H →* M) :
    ⁅f.range, f.range⁆ = f.range :=
  Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective (f := f.rangeRestrict)
    f.rangeRestrict_surjective)

theorem lc2At_sp4T (hF : 4 ≤ Nat.card F) : LC2At (KFacts.sp4T F) := by
  have h3 := three_ne_zero_of_charTwo (F := F)
  haveI := isPerfect_sl2 hF
  refine lc2At_of_commutator (S := (KFacts.planeSp (F := F) 1).range) ?_
    (commutator_range_eq _) fun x hx y hy => ?_
  · rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (KFacts.planeSp_commute _ _).symm
  · set φ := (KFacts.block0Hom F h3).toHomUnits with hφ
    have hcomm : φ ⟨x, hx⟩ * φ ⟨y, hy⟩ = φ ⟨y, hy⟩ * φ ⟨x, hx⟩ := by
      apply Units.ext
      simp only [Units.val_mul, hφ, MonoidHom.coe_toHomUnits, KFacts.block0Hom_apply]
      exact KFacts.commute_of_commute_ordThreeMat
        (KFacts.block0_mul_ordThreeMat h3 (KFacts.mul_planeBlock_eq_of_mem_centralizer hx))
        (KFacts.block0_mul_ordThreeMat h3 (KFacts.mul_planeBlock_eq_of_mem_centralizer hy))
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({KFacts.sp4T F} : Set (StatedSp 2 F)) :=
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    have h1 : φ ⟨x * y * x⁻¹ * y⁻¹, hxy⟩ = 1 := by
      have e : (⟨x * y * x⁻¹ * y⁻¹, hxy⟩ : Subgroup.centralizer ({KFacts.sp4T F} : Set _)) =
          ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h1' := congrArg Units.val h1
    rw [hφ, MonoidHom.coe_toHomUnits, KFacts.block0Hom_apply, Units.val_one] at h1'
    exact KFacts.mem_range_planeSp_one h3 hxy h1'

theorem lc2At_yT (hF : 4 ≤ Nat.card F) : LC2At (Item84KFacts4.yT F) := by
  haveI := isPerfect_sl2 hF
  exact lc2At_of_commutator Item84KFacts4.range_levi_le_centralizer (commutator_range_eq _)
    fun x hx y hy => Item84KFacts4.commutator_mem_range_levi hx hy

theorem lc2At_sp4 (hF : 4 ≤ Nat.card F) {y : StatedSp 2 F} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    LC2At y := by
  by_cases hN : ∃ u, Item84KFacts4.nMat y *ᵥ u ≠ 0
  · obtain ⟨g, hg⟩ := Item84KFacts4.exists_conj_sp4T hy3 hy1 hN
    refine LC2At.of_mulEquiv (MulAut.conj g⁻¹) ?_
    have : (MulAut.conj g⁻¹ : StatedSp 2 F ≃* StatedSp 2 F) y = KFacts.sp4T F := by
      rw [MulAut.conj_apply, ← hg]
      group
    rw [this]
    exact lc2At_sp4T hF
  · push Not at hN
    obtain ⟨g, hg⟩ := Item84KFacts4.exists_conj_yT hy3 hy1 hN
    refine LC2At.of_mulEquiv (MulAut.conj g⁻¹) ?_
    have : (MulAut.conj g⁻¹ : StatedSp 2 F ≃* StatedSp 2 F) y = Item84KFacts4.yT F := by
      rw [MulAut.conj_apply, ← hg]
      group
    rw [this]
    exact lc2At_yT hF

@[expose] noncomputable def projSpEquiv : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
  MulEquiv.ofBijective (proj 2 F) ⟨KFacts.proj_injective_of_charTwo,
    QuotientGroup.mk'_surjective _⟩

end Sp4

section Models

theorem innerFacts_statedProj_eight :
    InnerFacts (StatedProj (StatedSp 2 (GaloisField 2 3))) := by
  have hF : Nat.card (GaloisField 2 3) = 8 := by rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  have hF4 : 4 ≤ Nat.card (GaloisField 2 3) := by rw [hF]; norm_num
  haveI : CharP (GaloisField 2 3) 2 := inferInstance
  refine ⟨fun z hz => ?_, fun τ hτ g hg3 hg1 hτg => ?_, fun g hg3 hg1 => ?_⟩
  · have hc : z ∈ Subgroup.center (StatedProj (StatedSp 2 (GaloisField 2 3))) :=
      Subgroup.mem_center_iff.mpr fun y => (hz y).symm
    have hc' : projSpEquiv.symm z ∈ Subgroup.center (StatedSp 2 (GaloisField 2 3)) :=
      Subgroup.mem_center_iff.mpr fun y => by
        apply projSpEquiv.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact (Subgroup.mem_center_iff.mp hc (projSpEquiv y))
    rw [KFacts.center_statedSp_eq_bot, Subgroup.mem_bot] at hc'
    rw [← MulEquiv.apply_symm_apply projSpEquiv z, hc', map_one]
  · obtain ⟨k, hk⟩ := hτ
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective
      ((StatedScalars (Fin 2 ⊕ Fin 2) (GaloisField 2 3)).subgroupOf
        (StatedSp 2 (GaloisField 2 3))) g
    have he3 : e ^ 3 = 1 := KFacts.proj_injective_of_charTwo (by
      change proj 2 _ (e ^ 3) = proj 2 _ 1
      rw [map_pow, map_one]
      exact hg3)
    have he1 : e ≠ 1 := by
      rintro rfl
      exact hg1 (map_one _)
    exact Sec4.Item434SmallTwoIII.mem_range_conj_of_fixed hk
      (fun h => by
        have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
        omega)
      he3 he1 hτg
  · refine LC2At.of_mulEquiv projSpEquiv.symm ?_
    have he3 : projSpEquiv.symm g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    have he1 : projSpEquiv.symm g ≠ 1 := fun h1 =>
      hg1 (projSpEquiv.symm.injective (h1.trans (map_one _).symm))
    exact lc2At_sp4 hF4 he3 he1

theorem innerFacts_projSp_eight : InnerFacts (projSp 2 (GaloisField 2 (3 * 1))) :=
  InnerFacts.of_mulEquiv
    (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
      (StatedSp 2 (GaloisField 2 3))).symm innerFacts_statedProj_eight

theorem perfFacts_reeGamma {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * 1 + 1)) :
    PerfFacts (CFSG.LieType.Ree.ReeTag.F4.reeGamma K 1) := by
  have hZ := CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial 1 K hK
  refine ⟨fun z hz => ?_, fun g hg3 hg1 => ?_⟩
  · have : z ∈ Subgroup.center (CFSG.LieType.Ree.ReeTag.F4.reeGamma K 1) :=
      Subgroup.mem_center_iff.mpr fun y => (hz y).symm
    rwa [hZ, Subgroup.mem_bot] at this
  · have hq := Sec19.SimsC198.reeGamma_isQuasisimple_centralizer le_rfl hK g
      (orderOf_eq_prime hg3 hg1)
    rw [inSubgroup_perfectResidual_of_isPerfect hq.1]

end Models

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
