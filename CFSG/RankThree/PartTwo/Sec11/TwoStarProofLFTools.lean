module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini
public import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree
open CFSG.RankThree.PartOne.FixedRank36 (fixedSub frattiniRep)
open scoped IsMulCommutative commutatorElement

namespace TwoStarProof

theorem eq_one_of_perfect_of_mem_pGroup {X M : Type*} [Group X] [Group M] [Finite M]
    [Group.IsPerfect X] (f : X →* M) {K : Subgroup M} {p : ℕ} [Fact p.Prime] (hK : IsPGroup p K)
    (hf : ∀ x, f x ∈ K) (x : X) : f x = 1 := by
  by_contra hx
  have hR : IsPGroup p f.range := hK.to_le (by rintro _ ⟨y, rfl⟩; exact hf y)
  have : Group.IsPerfect f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have : Nontrivial f.range := ⟨⟨⟨f x, x, rfl⟩, 1, fun h => hx (congrArg Subtype.val h)⟩⟩
  have : Group.IsNilpotent f.range := hR.isNilpotent
  exact Group.IsPerfect.not_isSolvable f.range inferInstance

theorem exists_two_element_lift {X Y : Type*} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) {y : Y} (hy : y * y = 1) :
    ∃ x : X, π x = y ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨x₀, rfl⟩ := hπ y
  obtain ⟨k, n, hn, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  refine ⟨x₀ ^ n, ?_, k, ?_⟩
  · obtain ⟨j, rfl⟩ := hn
    rw [map_pow, pow_succ, pow_mul, sq, hy, one_pow, one_mul]
  · rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]

theorem eigenspace_one_eq_ker {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) : Module.End.eigenspace f 1 = LinearMap.ker (f - 1) := by
  rw [Module.End.eigenspace_def, one_smul]

theorem isPGroup_zpowers_of_pow {M : Type*} [Group M] {x : M} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hj, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hx, one_zpow]

section Critical

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P] {X : Type*} [Group X]
  [Group.IsPerfect X]

theorem exists_critical_rep_ne_one (hp2 : p ≠ 2) (hP : IsPGroup p P) (ρ : X →* MulAut P)
    (hρ : ∃ x, ρ x ≠ 1) :
    ∃ (D : Subgroup P) (_ : D.Characteristic), IsPGroup p D ∧ (∀ x : D, x ^ p = 1) ∧
      commutator D ≤ Subgroup.center D ∧
      ∃ (_ : IsElementaryAbelian p (D ⧸ frattini D)),
        ∃ x, frattiniRep p ((Sec3.restrictCharacteristic D).comp ρ) x ≠ 1 := by
  obtain ⟨x₀, hx₀⟩ := hρ
  have : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hx₀ (MulEquiv.ext fun y => Subsingleton.elim _ _)
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hP
  have hDp : IsPGroup p D := hP.to_subgroup D
  obtain ⟨-, -, -, hel, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  set ρD := (Sec3.restrictCharacteristic D).comp ρ with hρD
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by simpa using hDexp x x.2)
  have hclass : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hDcomm (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top (b : P)))
    have h2 := Subgroup.mem_centralizer_iff.mp h1.2 g g.2
    apply Subtype.ext
    simpa [commutatorElement_def] using h2
  refine ⟨D, hDchar, hDp, hexp, hclass, hel, ?_⟩
  by_contra hall
  push Not at hall
  have hD1 : ∀ x, ρD x = 1 := by
    refine eq_one_of_perfect_of_mem_pGroup ρD
      (CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup p hDp)
      fun x => ?_
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro w
    have h1 := congrArg (fun f => f (Additive.ofMul (QuotientGroup.mk' (frattini D) w))) (hall x)
    simp only [Module.End.one_apply] at h1
    rw [show Additive.ofMul (QuotientGroup.mk' (frattini D) w) =
      Additive.ofMul ((w : D) : D ⧸ frattini D) from rfl,
      CFSG.RankThree.PartOne.FixedRank36.frattiniRep_apply] at h1
    exact congrArg Additive.toMul h1
  have hP1 : ∀ x, ρ x = 1 := by
    refine eq_one_of_perfect_of_mem_pGroup ρ hDfix fun x => ?_
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut D => ((φ ⟨y, hy⟩ : D) : P)) (hD1 x)
    simpa [hρD, Sec3.restrictCharacteristic_apply_coe] using h1
  exact hx₀ (hP1 x₀)

omit [Group.IsPerfect X] in
theorem three_le_pRank_fixed {D : Type*} [Group D] [Finite D]
    [IsElementaryAbelian p (D ⧸ frattini D)] (hp2 : p ≠ 2) (hD : IsPGroup p D)
    (hexp : ∀ x : D, x ^ p = 1) (hclass : commutator D ≤ Subgroup.center D)
    (ρ : X →* MulAut D) {t : X} {k : ℕ} (ht : t ^ 2 ^ k = 1)
    (hdim : 3 ≤ Module.finrank (ZMod p) (LinearMap.ker (frattiniRep p ρ t - 1))) :
    3 ≤ CFSG.pRank p (fixedSub (ρ t)) := by
  by_contra hlt
  push Not at hlt
  have hρt : (ρ t) ^ 2 ^ k = 1 := by rw [← map_pow, ht, map_one]
  have h := CFSG.RankThree.PartOne.FixedRank36.finrank_fixed_le hD hp2 hexp hclass ρ t
    (isPGroup_zpowers_of_pow hρt) (by omega)
  rw [eigenspace_one_eq_ker] at h
  omega

end Critical

end TwoStarProof

end CFSG.RankThree.PartTwo.Sec11
