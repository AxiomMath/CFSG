module

public import CFSG.Permutation.FiveTransitive.ExceptionalThreeAverage
public import CFSG.Permutation.FiveTransitive.FixedSetConjugateCounts

public section

namespace CFSG

namespace FiveTransitive.ExceptionalThreeConjugateAverage

open Equiv FixedSetConjugateCounts
open scoped BigOperators

theorem sum_eventCount_conjugates
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (g u : Perm X) (S : Finset X) (hS : S.card = 3) (hSA : S ⊆ g.support)
    {a c : X} (ha : a ∈ S) (hc : c ∈ g.support) (hcS : c ∉ S)
    (hmove : u a ≠ a) (hfix : ∀ x ∈ S, x ≠ a → u x = x) (hu3 : u ^ 3 = 1)
    [Fintype (Fixer P S)] :
    (∑ k : Fixer P S, ExceptionalThreeAverage.eventCount g (conjugate u k) a c) *
      ((Fintype.card X - 3) * (Fintype.card X - 4)) =
        2 * Nat.card (Fixer P S) * (Fintype.card X - g.support.card) := by
  have h2 := remainder_two_transitive P h5 S hS
  have hnot2 : u (u a) ≠ a := by
    intro he
    have hcube := DFunLike.congr_fun hu3 a
    have hcube' : u (u (u a)) = a := by
      simpa only [pow_succ, pow_zero, Perm.mul_apply, Perm.one_apply] using hcube
    rw [he] at hcube'
    exact hmove hcube'
  apply ExceptionalThreeAverage.sum_eventCount_mul
  · intro x hx
    have hxS : x ∉ S := fun hxS => hx (hSA hxS)
    have hcx : c ≠ x := fun h => hx (h ▸ hc)
    have hcount := card_neighbors_distinguished P S h2 u ha hmove hfix hnot2 hcS hxS hcx
    simpa only [hS, Nat.sub_sub, show (3 + 1 : ℕ) = 4 from rfl, mul_assoc] using hcount
  · intro x hx
    have hxS : x ∉ S := fun hxS => hx (hSA hxS)
    have hxc : x ≠ c := fun h => hx (h.symm ▸ hc)
    have hcount := card_neighbors_distinguished P S h2 u ha hmove hfix hnot2 hxS hcS hxc
    simpa only [hS, Nat.sub_sub, show (3 + 1 : ℕ) = 4 from rfl, mul_assoc] using hcount

end FiveTransitive.ExceptionalThreeConjugateAverage

end CFSG
