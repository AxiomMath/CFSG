module

public import CFSG.Permutation.FiveTransitive.FreeEvenOrderDivisibility
public import CFSG.Permutation.FiveTransitive.FixedComplementSign
public import CFSG.Permutation.FiveTransitive.FixedNormalizerCyclicPreimageSylow

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicEvenComplementDivisibility

open MulAction FixedNormalizerAction

theorem twice_card_dvd
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (Q : Subgroup G) (hcyclic : IsCyclic Q) (hcard : Even (Nat.card Q))
    (heven : ∀ q : Q, Equiv.Perm.sign (toPerm q.val : Equiv.Perm X) = 1)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1) :
    2 * Nat.card Q ∣ Nat.card X - (fixedPoints Q X).ncard := by
  classical
  let _ := Fintype.ofFinite (Fixed (X := X) Q)
  let _ := Fintype.ofFinite (NormalizerFixedComplement.Domain (X := X) Q)
  let _ : IsCyclic Q := hcyclic
  obtain ⟨q, hq⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  let n : Normalizer Q := ⟨q.val, Q.le_normalizer q.property⟩
  let i : Inside Q := ⟨n, q.property⟩
  have hi : orderOf i = Nat.card Q := by
    have hiG : orderOf i = orderOf q.val :=
      (orderOf_injective (Inside Q).subtype Subtype.val_injective i).symm.trans
        (orderOf_injective (Normalizer Q).subtype Subtype.val_injective n).symm
    exact hiG.trans ((Subgroup.orderOf_coe q).trans hq)
  have hlocal : (toPerm n : Equiv.Perm (Fixed (X := X) Q)) = 1 :=
    FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q q.property
  have hsign : (toPerm n : Equiv.Perm (NormalizerFixedComplement.Domain (X := X) Q)).sign = 1 := by
    have h := FixedComplementSign.sign_product (X := X) Q n
    rw [hlocal, map_one, one_mul] at h
    exact h.trans (heven q)
  have hdiv := FreeEvenOrderDivisibility.twice_order_dvd
    (NormalizerFixedComplement.free_inside Q hfree) i (hi.symm ▸ hcard) hsign
  rw [hi, NormalizerFixedComplement.card_domain] at hdiv
  exact hdiv

end FiveTransitive.CyclicEvenComplementDivisibility

end CFSG
