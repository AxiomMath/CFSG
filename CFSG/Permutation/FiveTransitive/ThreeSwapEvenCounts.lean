module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard
public import CFSG.Permutation.FiveTransitive.NormalizerEvenCoset

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.ThreeSwapEvenCounts

open MulAction FixedNormalizerAction

theorem local_five
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (u : Normalizer Q) (v w : Fixed (X := X) Q) (hne : v ≠ w)
    (hu : toPermHom (Normalizer Q) (Fixed (X := X) Q) u = Equiv.swap v w) :
    (fixedBy X (u : G) ∩ fixedPoints Q X).ncard = 5 := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  rw [← FixedNormalizerLocalCard.fixed_card Q u, hu, Nat.card_eq_fintype_card,
    Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType,
    Equiv.Perm.card_support_swap hne, ← Nat.card_eq_fintype_card, hseven]

theorem coset_outside_two
    {G X : Type*} [Group G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (B : Subgroup (Normalizer Q)) (hIB : Inside Q ≤ B)
    (hsq : ∀ b : B, b ^ 2 = 1)
    (u : B) (v w : Fixed (X := X) Q) (hne : v ≠ w)
    (hu : toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val = Equiv.swap v w)
    (q : Inside Q) :
    (fixedBy X (((q : Normalizer Q) * u.val) : G) \ fixedPoints Q X).ncard = 2 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hfq : f (q : Normalizer Q) = 1 := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    exact mem_fixedPoints.mp z.property q
  have hlocal : (fixedBy X (u.val : G) ∩ fixedPoints Q X).ncard = 5 :=
    local_five Q hseven u.val v w hne hu
  have hqpow : ((q : Normalizer Q) * u.val) ^ 2 = 1 :=
    congrArg Subtype.val (hsq ⟨(q : Normalizer Q) * u.val, B.mul_mem (hIB q.property) u.property⟩)
  have hqne : (q : Normalizer Q) * u.val ≠ 1 := by
    intro he
    have hf := congrArg f he
    change f u.val = Equiv.swap v w at hu
    rw [map_mul, hfq, one_mul, map_one, hu] at hf
    exact hne (Equiv.swap_eq_one_iff.mp hf)
  have hqo : orderOf ((q : Normalizer Q) * u.val) = 2 := orderOf_eq_prime hqpow hqne
  have h := NormalizerEvenCoset.fixed_card_eq_two heven hdegree hmax Q u.val hlocal q hqo
  rwa [NormalizerFixedComplement.fixed_card] at h

end FiveTransitive.ThreeSwapEvenCounts

end CFSG
