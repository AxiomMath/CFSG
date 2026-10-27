module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.FaithfulNormalizerFixedDegree

open MulAction FixedNormalizerAction

private theorem fixed_eq_univ_iff
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] (Q : Subgroup G) :
    fixedPoints Q X = Set.univ ↔ Q = ⊥ := by
  constructor
  · intro h
    apply bot_unique
    intro q hq
    change q = 1
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    have hx : x ∈ fixedPoints Q X := by rw [h]; trivial
    simpa only [one_smul, Subgroup.smul_def] using mem_fixedPoints.mp hx ⟨q, hq⟩
  · intro h
    subst Q
    apply Set.eq_univ_of_forall
    intro x q
    change q.val • x = x
    have hq : q.val = 1 := q.property
    rw [hq, one_smul]

private theorem card_lt_of_ne_bot
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [Finite X]
    (Q : Subgroup G) (hQ : Q ≠ ⊥) : Nat.card (Fixed (X := X) Q) < Nat.card X := by
  rw [fixed_eq, Nat.card_coe_set_eq]
  apply Set.ncard_lt_card
  exact fun h => hQ ((fixed_eq_univ_iff Q).mp h)

theorem degree_cases
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [Finite X]
    (Q : Subgroup G) :
    (Q = ⊥ ∧ Nat.card (Fixed (X := X) Q) = Nat.card X) ∨
      (Q ≠ ⊥ ∧ Nat.card (Fixed (X := X) Q) < Nat.card X) := by
  classical
  by_cases hQ : Q = ⊥
  · left
    refine ⟨hQ, ?_⟩
    rw [fixed_eq, (fixed_eq_univ_iff Q).mpr hQ, Nat.card_coe_set_eq, Set.ncard_univ]
  · exact Or.inr ⟨hQ, card_lt_of_ne_bot Q hQ⟩

end FiveTransitive.FaithfulNormalizerFixedDegree

end CFSG
