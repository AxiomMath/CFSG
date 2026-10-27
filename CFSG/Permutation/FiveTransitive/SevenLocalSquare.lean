module

public import CFSG.Permutation.FiveTransitive.SevenFivePermutationSquare
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm
public import CFSG.Permutation.FiveTransitive.TwoGroupCosetFixedBound

public section

namespace CFSG

namespace FiveTransitive.SevenLocalSquare

open MulAction FixedSetNormalizerPerm

theorem square_fixes
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (h7 : Nat.card (fixedPoints Q X) = 7)
    (x : G) (hx : x ∈ Subgroup.normalizer (Q : Set G))
    (h5 : (fixedBy X x ∩ fixedPoints Q X).ncard = 5) :
    ∀ z ∈ fixedPoints Q X, x ^ 2 • z = z := by
  classical
  let _ : Fintype (fixedPoints Q X) := Fintype.ofFinite _
  let f := fixedPerm G X Q x hx
  let e : Function.fixedPoints f ≃ ↥(fixedBy X x ∩ fixedPoints Q X) :=
    { toFun := fun y => ⟨y.val.val, congrArg Subtype.val y.property, y.val.property⟩
      invFun := fun y => ⟨⟨y.val, y.property.2⟩, Subtype.ext y.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hf5 : Nat.card (Function.fixedPoints f) = 5 :=
    (Nat.card_congr e).trans (by rw [Nat.card_coe_set_eq, h5])
  have hf := (SevenFivePermutationSquare.isSwap_and_square h7 f hf5).2
  intro z hz
  have he := congrArg (fun g : Equiv.Perm (fixedPoints Q X) => (g ⟨z, hz⟩).val) hf
  change ((fixedPerm G X Q x hx ^ 2) ⟨z, hz⟩).val = z at he
  rwa [fixedPerm_pow_apply_val] at he

theorem coset_square_fixes
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (h7 : Nat.card (fixedPoints Q X) = 7)
    (x : G) (hx : x ∈ Subgroup.normalizer (Q : Set G))
    (h5 : (fixedBy X x ∩ fixedPoints Q X).ncard = 5) :
    ∀ q : Q, ∀ z ∈ fixedPoints Q X, ((q : G) * x) ^ 2 • z = z := by
  intro q
  apply square_fixes Q h7 ((q : G) * x)
    ((Subgroup.normalizer (Q : Set G)).mul_mem (Q.le_normalizer q.property) hx)
  rw [TwoGroupCosetFixedBound.coset_fixed_inter Q q x]
  exact h5

end FiveTransitive.SevenLocalSquare

end CFSG
