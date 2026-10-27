module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions
public import CFSG.Monster.Existence.Compat.Sp8

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.PresentationLocal CFSG.ComponentClassification.StandardRecognition
  CFSG.Monster.Existence.Compat
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LieType.SteinbergBR (solvableRadical_map_equiv not_isSolvable_of_isPerfect)
open scoped commutatorElement

theorem solvableRadical_eq_bot_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [Group.IsPerfect G] : solvableRadical G = ⊥ := by
  have hnorm : (solvableRadical G).Normal := inferInstance
  have hsol : Group.IsSolvable (solvableRadical G) := CFSG.ABGLocalTools.solvableRadical_isSolvable
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    rw [h] at hsol
    have : Group.IsSolvable G := Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) (MulEquiv.surjective _)
    exact not_isSolvable_of_isPerfect this

theorem solvableRadical_sympFour : solvableRadical sympFour = ⊥ := by
  set R := solvableRadical sympFour with hR
  have hnorm : R.Normal := inferInstance
  have hG' : (commutator sympFour).Normal := inferInstance
  have hsimp : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
  have hperf : Group.IsPerfect ↥(commutator sympFour) := isPerfect_commutator_sympFour
  have hnt : Nontrivial ↥(commutator sympFour) := hsimp.toNontrivial
  have hsub : R.subgroupOf (commutator sympFour) = ⊥ := by
    rcases (inferInstance : (R.subgroupOf (commutator sympFour)).Normal).eq_bot_or_eq_top with
      h | h
    · exact h
    · exfalso
      have hle : commutator sympFour ≤ R := Subgroup.subgroupOf_eq_top.mp h
      have : Group.IsSolvable ↥R := CFSG.ABGLocalTools.solvableRadical_isSolvable
      have : Group.IsSolvable ↥(commutator sympFour) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      exact not_isSolvable_of_isPerfect this
  have hcomm : ∀ x ∈ R, ∀ h ∈ commutator sympFour, h * x = x * h := by
    intro x hx h hh
    have h1 : x * h⁻¹ * x⁻¹ ∈ commutator sympFour := hG'.conj_mem _ (inv_mem hh) x
    have hcG : x * h⁻¹ * x⁻¹ * h ∈ commutator sympFour := mul_mem h1 hh
    have hcR : x * h⁻¹ * x⁻¹ * h ∈ R := by
      have h2 : h⁻¹ * x⁻¹ * h⁻¹⁻¹ ∈ R := hnorm.conj_mem _ (inv_mem hx) h⁻¹
      rw [inv_inv] at h2
      rw [mul_assoc, mul_assoc, ← mul_assoc h⁻¹]
      exact mul_mem hx h2
    have hmem : (⟨x * h⁻¹ * x⁻¹ * h, hcG⟩ : ↥(commutator sympFour)) ∈
        R.subgroupOf (commutator sympFour) := hcR
    rw [hsub, Subgroup.mem_bot] at hmem
    have h3 : x * h⁻¹ * x⁻¹ * h = 1 := congrArg Subtype.val hmem
    have h4 : ⁅x, h⁻¹⁆ = 1 := by
      rw [commutatorElement_def, inv_inv]
      exact h3
    have h5 : Commute x h⁻¹ := commutatorElement_eq_one_iff_commute.mp h4
    exact (h5.inv_right.eq).symm
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxc : x ∈ Subgroup.centralizer (commutator sympFour : Set sympFour) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => hcomm x hx h hh
  rw [centralizer_commutator_sympFour] at hxc
  exact hxc

variable {r : ℕ} {K : Type} [Field K]

theorem simple_perfect_statedProj {k : Type} [Field k] [Finite k] (hr : 2 ≤ r)
    (hne : ¬(r = 2 ∧ Nat.card k = 2)) :
    IsSimpleGroup (StatedProj (StatedSp r k)) ∧ Group.IsPerfect (StatedProj (StatedSp r k)) := by
  have hq2 : 2 ≤ Nat.card k := Finite.one_lt_card
  have hcard4 : 4 ≤ Nat.card k → ∃ s : Finset k, s.card = 4 := by
    intro h4
    have := Fintype.ofFinite k
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  have hcases : 4 ≤ Nat.card k ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨ (Nat.card k = 2 ∧ 3 ≤ r) := by
    by_cases h4 : 4 ≤ Nat.card k
    · exact Or.inl h4
    · right
      have h23 : Nat.card k = 2 ∨ Nat.card k = 3 := by omega
      rcases h23 with h2 | h3
      · exact Or.inr ⟨h2, by
          by_contra h3
          exact hne ⟨by omega, h2⟩⟩
      · exact Or.inl ⟨h3, hr⟩
  refine ⟨CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) ?_,
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r k ?_⟩
  · rcases hcases with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · rcases hcases with h | h
    · exact Or.inl (hcard4 h)
    · exact Or.inr h

@[expose] noncomputable def statedProjEquivSympFour {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) : StatedProj (StatedSp 2 k) ≃* sympFour :=
  (statedProjEquivOfBot (StatedSp 2 k) (statedScalars_eq_bot hk)).trans
    ((statedSpEquiv 2 k).trans ((sympMapEquiv (ringEquivZMod2 hk)).trans
      (MulEquiv.ofBijective symplecticToSympFour symplecticToSympFour_bijective)))

theorem solvableRadical_statedProj_eq_bot {k : Type} [Field k] [Finite k] (hr : 2 ≤ r) :
    solvableRadical (StatedProj (StatedSp r k)) = ⊥ := by
  by_cases hex : r = 2 ∧ Nat.card k = 2
  · obtain ⟨rfl, hk⟩ := hex
    have h := solvableRadical_map_equiv (statedProjEquivSympFour hk).symm
    rw [solvableRadical_sympFour, Subgroup.map_bot] at h
    exact h.symm
  · obtain ⟨hs, hp⟩ := simple_perfect_statedProj (k := k) hr hex
    exact solvableRadical_eq_bot_of_simple

theorem solvableRadical_fixedGroup [Finite K] (hr : 2 ≤ r) {p : ℕ} (hp : Odd p) {σ : K ≃+* K}
    (hσp : σ ^ p = 1) : solvableRadical ↥(spFixedGroup (fieldAut r K σ)) = ⊥ := by
  have : NeZero r := ⟨by omega⟩
  have hP : solvableRadical (StatedProj (StatedSp r (descentField σ))) = ⊥ :=
    solvableRadical_statedProj_eq_bot hr
  have h1 := solvableRadical_map_equiv (MonoidHom.ofInjective (subfieldInj_injective (r := r) σ))
  rw [hP, Subgroup.map_bot] at h1
  rw [spFixedGroup_fieldAut_eq_range hp hσp, ← range_subfieldInj (r := r) σ]
  exact h1.symm

end CFSG.RankThree.PartOne.KCSpComm
