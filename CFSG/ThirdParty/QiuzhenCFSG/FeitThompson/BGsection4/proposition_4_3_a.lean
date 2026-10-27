module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Infrastructure

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

section Main

public theorem CFSG.proposition_4_3_a {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    (hclass : NilpotencyClassLe 2 R ∨ (3 < p ∧ NilpotencyClassLe 3 R)) :
    Monoid.exponent ↥(omega₁ (G := R) (p := p)) = 1 ∨
      Monoid.exponent ↥(omega₁ (G := R) (p := p)) = p := by
  have hexp_dvd :
      Monoid.exponent ↥(omega₁ (G := R) (p := p)) ∣ p := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    change (x : R) ^ p = 1
    refine Subgroup.closure_induction (k := {z : R | z ^ (p ^ 1) = 1}) (x := x.1) ?_ ?_ ?_ ?_ x.2
    · intro z hz
      simpa [pow_one] using hz
    · simp
    · intro z₁ z₂ _hz₁ _hz₂ hz₁ hz₂
      cases hclass with
      | inl hclass2 =>
          have hcomm_le :
              ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ ≤ Subgroup.center R :=
            commutator_le_center_of_le_upperCentralSeries_two (G := R) (⊤ : Subgroup R)
              (by simpa [hclass2])
          have hcomm_mem : ⁅z₂, z₁⁆ ∈ Subgroup.center R := by
            exact hcomm_le (Subgroup.commutator_mem_commutator (by simp) (by simp))
          simpa using
            (pth_mul_eq_one_of_class2 (G := R) (p := p) hpodd z₁ z₂ hcomm_mem hz₁ hz₂)
      | inr hclass3 =>
          simpa using
            (pth_mul_eq_one_of_class3 (R := R) (p := p) hpodd hclass3.1 hclass3.2 hz₁ hz₂)
    · intro z _hz hz
      simpa [inv_pow] using congrArg Inv.inv hz
  rcases (show Nat.Prime p from Fact.out).eq_one_or_self_of_dvd _ hexp_dvd with h1 | hp
  · exact Or.inl h1
  · exact Or.inr hp


end Main
