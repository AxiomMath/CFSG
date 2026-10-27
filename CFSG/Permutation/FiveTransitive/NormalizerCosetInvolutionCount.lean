module

public import CFSG.Permutation.FiveTransitive.NormalizerEvenCoset
public import CFSG.Permutation.FiveTransitive.SevenLocalSquare
public import CFSG.Permutation.FiveTransitive.CosetFixedSquare

public section

namespace CFSG

namespace FiveTransitive.NormalizerCosetInvolutionCount

open MulAction NormalizerFixedComplement
open scoped BigOperators

theorem fixed_iff_order_two
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (q : Inside Q) :
    (Nat.card (fixedBy (Domain (X := X) Q) ((q : Normalizer Q) * x)) ≠ 0 ↔
      orderOf ((q : Normalizer Q) * x) = 2) ∧
    (Nat.card (fixedBy (Domain (X := X) Q) ((q : Normalizer Q) * x)) = 0 ∨
      Nat.card (fixedBy (Domain (X := X) Q) ((q : Normalizer Q) * x)) = 2) := by
  have hforward (hpos : Nat.card (fixedBy (Domain (X := X) Q) ((q : Normalizer Q) * x)) ≠ 0) :
      orderOf ((q : Normalizer Q) * x) = 2 := by
    obtain ⟨z, hz⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hpos)).1
    let g : A := ⟨q.val.val * x.val, A.mul_mem (hQA q.property) hx⟩
    have hF : (fixedPoints Q X).ncard = 7 := by
      simpa only [Nat.card_coe_set_eq] using hseven
    have hsq := CosetFixedSquare.eq_one_of_maximal_fixed 7 hmax A hA g
      (fixedPoints Q X) hF
      (SevenLocalSquare.coset_square_fixes Q hseven x.val x.property hlocal ⟨q.val.val, q.property⟩)
      z.val z.property (congrArg Subtype.val hz)
    have hn : (q : Normalizer Q) * x ≠ 1 := by
      intro he
      have he' : q.val.val * x.val = 1 := congrArg Subtype.val he
      apply hxQ
      rw [eq_inv_of_mul_eq_one_right he']
      exact Q.inv_mem q.property
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime_iff.mpr
    exact ⟨Subtype.ext hsq, hn⟩
  have hbackward := NormalizerEvenCoset.fixed_card_eq_two heven hdegree hmax Q x hlocal q
  refine ⟨⟨hforward, fun h => by rw [hbackward h]; omega⟩, ?_⟩
  by_cases hzero : Nat.card (fixedBy (Domain (X := X) Q) ((q : Normalizer Q) * x)) = 0
  · exact Or.inl hzero
  · exact Or.inr (hbackward (hforward hzero))

end FiveTransitive.NormalizerCosetInvolutionCount

end CFSG
