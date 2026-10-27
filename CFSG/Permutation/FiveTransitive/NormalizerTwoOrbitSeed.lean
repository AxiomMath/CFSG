module

public import CFSG.Permutation.FiveTransitive.NormalizerTwoOrbitCardTwo

public section

namespace CFSG

namespace FiveTransitive.NormalizerTwoOrbitSeed

open MulAction FixedNormalizerAction

theorem card_two_involution_coset
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) :
    Nat.card Q = 2 ∧ orderOf x.val = 2 ∧
      ∀ q : Q, (fixedBy X (q.val * x.val) \ fixedPoints Q X).ncard = 2 := by
  have hc := NormalizerTwoOrbitCardTwo.cyclic_and_card_eq_two
    heven hdegree hmax Q A hQA hA hQ hne hseven hfree S hS himage x hx hxQ hlocal horbits
  have hsq := NormalizerTwoOrbitCyclic.coset_square_eq_one
    hmax Q A hQA hA hseven hfree x hx hxQ hlocal horbits
  have hx2 : x.val ^ 2 = 1 := by simpa only [one_mul] using hsq 1 Q.one_mem
  have hxne : x.val ≠ 1 := fun he => hxQ (he ▸ Q.one_mem)
  refine ⟨hc.2, orderOf_eq_prime_iff.mpr ⟨hx2, hxne⟩, ?_⟩
  intro q
  let qi : Inside Q := ⟨⟨q.val, Q.le_normalizer q.property⟩, q.property⟩
  have hh := NormalizerSevenOrbitCount.saturated_coset_fixed_two
    hmax Q A hQA hA hfree x hx hxQ hlocal horbits qi
  rw [NormalizerFixedComplement.fixed_card] at hh
  exact hh

end FiveTransitive.NormalizerTwoOrbitSeed

end CFSG
