module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.SevenFivePermutationSquare

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.FixedNormalizerLocalCard

open MulAction FixedNormalizerAction

theorem fixed_card
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (x : Normalizer Q) :
    Nat.card (Function.fixedPoints (toPermHom (Normalizer Q) (Fixed (X := X) Q) x)) =
      (fixedBy X x.val ∩ fixedPoints Q X).ncard := by
  let e : Function.fixedPoints (toPermHom (Normalizer Q) (Fixed (X := X) Q) x) ≃
      ↥(fixedBy X x.val ∩ fixedPoints Q X) :=
    { toFun := fun y => ⟨y.val.val, congrArg Subtype.val y.property,
        (fixed_eq (X := X) Q ▸ y.val.property)⟩
      invFun := fun y => ⟨⟨y.val, (fixed_eq (X := X) Q).symm ▸ y.property.2⟩,
        Subtype.ext y.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq]

theorem isSwap
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (x : Normalizer Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5) :
    (toPermHom (Normalizer Q) (Fixed (X := X) Q) x).IsSwap := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  exact (SevenFivePermutationSquare.isSwap_and_square hseven
    (toPermHom (Normalizer Q) (Fixed (X := X) Q) x) ((fixed_card Q x).trans hlocal)).1

theorem not_mem_of_local_order_two
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (x : Normalizer Q)
    (hx : orderOf (toPermHom (Normalizer Q) (Fixed (X := X) Q) x) = 2) : x.val ∉ Q := by
  intro hxQ
  have he : toPermHom (Normalizer Q) (Fixed (X := X) Q) x = 1 := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    exact mem_fixedPoints.mp z.property ⟨x, hxQ⟩
  rw [he, orderOf_one] at hx
  contradiction

end FiveTransitive.FixedNormalizerLocalCard

end CFSG
