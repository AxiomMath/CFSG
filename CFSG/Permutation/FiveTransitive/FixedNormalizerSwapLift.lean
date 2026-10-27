module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerCompatibleSylow
public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup
public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.FixedNormalizerSwapLift

open MulAction FixedNormalizerAction

theorem exists_lift
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤) :
    ∃ (A : Subgroup G) (x : Normalizer Q), Q ≤ A ∧ IsPGroup 2 A ∧
      x.val ∈ A ∧ x.val ∉ Q ∧ (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5 := by
  classical
  let _ := Fintype.ofFinite (Fixed (X := X) Q)
  obtain ⟨e⟩ := (Function.Embedding.nonempty_iff_card_le (α := Fin 6)
    (β := Fixed (X := X) Q)).mpr (by
      simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_fin, hseven]
        using (by decide : 6 ≤ 7))
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  obtain ⟨P, hB, hIB, hmap, _⟩ := FixedNormalizerCompatibleSylow.exists_preimage
    Q S hS himage V (ThreeSwapTwoGroup.isTwoGroup e).1
  let B := SylowPreimageNormalizer.ambient f V P
  have ht : Equiv.swap (e 0) (e 1) ∈ B.map f := by
    rw [hmap]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨x, hxB, hxf⟩ := ht
  let A := B.map (Normalizer Q).subtype
  have hswap : (f x).IsSwap := by
    rw [hxf]
    exact ⟨e 0, e 1, e.injective.ne (by decide), rfl⟩
  refine ⟨A, x, ?_, hB.map _, ⟨x, hxB, rfl⟩,
    FixedNormalizerLocalCard.not_mem_of_local_order_two Q x hswap.orderOf, ?_⟩
  · intro q hq
    exact ⟨⟨q, Q.le_normalizer hq⟩, hIB hq, rfl⟩
  · rw [← FixedNormalizerLocalCard.fixed_card Q x]
    rw [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints, Equiv.Perm.isSwap_iff_cycleType.mp hswap]
    rw [← Nat.card_eq_fintype_card, hseven]
    rfl

end FiveTransitive.FixedNormalizerSwapLift

end CFSG
