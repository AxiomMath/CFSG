module

import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)
open scoped commutatorElement

namespace Proof17Res6

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_sup_theta {c : G} (hc3 : c ^ 3 = 1) {X : Subgroup G}
    (hcX : c ∈ Subgroup.normalizer (X : Set G))
    (hXc : ⁅X, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X) :
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  have hθc : θ.Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.1
  have : θ.Normal := Subgroup.normal_of_characteristic _
  have hcp : IsPGroup 3 (Subgroup.zpowers c) := Proof171.isPGroup_zpowers_of_pow_three hc3
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr hcX
  set f : ↥X →* ↥X ⧸ θ := QuotientGroup.mk' θ with hf
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    exact hθ3
  have hmemθ : ∀ u : ↥X, u ∈ θ ↔ (u : G) ∈ inSubgroup (aschbacherSolvableCore 3) X := fun u =>
    (Subgroup.mem_map_iff_mem X.subtype_injective).symm
  have htriv : ∀ (m : ↥(Subgroup.zpowers c)) (x : ↥X), f ⟨m * x * (m : G)⁻¹,
      Subgroup.le_normalizer_iff.mp hN m m.property x x.property⟩ = f x := by
    intro m x
    rw [hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hmemθ]
    have h1 := hXc (Subgroup.commutator_mem_commutator (inv_mem x.2) m.2)
    have e : (⁅(x : G)⁻¹, (m : G)⁆)⁻¹ =
        (((⟨m * x * (m : G)⁻¹, Subgroup.le_normalizer_iff.mp hN m m.property x x.property⟩ :
          ↥X)⁻¹ * x : ↥X) : G) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← e]
    exact inv_mem h1
  intro x hx
  obtain ⟨x', hx'C, hx'e⟩ := exists_centralizer_with_same_image_of_trivial_quotient_action 3
    Nat.prime_three (Subgroup.zpowers c) X hcp hN f hker htriv ⟨x, hx⟩
  have hθx : ((x' : G))⁻¹ * x ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    rw [hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hmemθ] at hx'e
    simpa using hx'e
  have hx'c : (x' : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)) hx'C
  have e : x = (x' : G) * ((x' : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ⟨x'.2, hx'c⟩ hθx

end Proof17Res6

end CFSG.RankThree.PartTwo.Sec17
