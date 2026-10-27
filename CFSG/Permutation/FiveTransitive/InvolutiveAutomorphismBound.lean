module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG

namespace FiveTransitive.InvolutiveAutomorphismBound

theorem card_le_fixed_sq
    (Q : Type*) [CommGroup Q] [Finite Q]
    (f : Q →* Q) (hf : Function.Involutive f)
    (h2 : ∀ q : Q, q * q = 1) :
    Nat.card Q ≤ (Nat.card {q : Q // f q = q}) ^ 2 := by
  let d : Q →* Q := f * MonoidHom.id Q
  have hd (q : Q) : d q = f q * q := rfl
  have hker (q : Q) : q ∈ d.ker ↔ f q = q := by
    change f q * q = 1 ↔ f q = q
    constructor
    · intro h
      apply mul_right_cancel (b := q)
      exact h.trans (h2 q).symm
    · intro h
      rw [h, h2]
  have hrange : d.range ≤ d.ker := by
    rintro q ⟨x, rfl⟩
    rw [hker, hd, map_mul, hf]
    exact mul_comm _ _
  have hkcard : Nat.card d.ker = Nat.card {q : Q // f q = q} :=
    Nat.card_congr
      { toFun := fun q => ⟨q, (hker q).mp q.property⟩
        invFun := fun q => ⟨q, (hker q).mpr q.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  calc
    Nat.card Q = Nat.card d.ker * Nat.card d.range := by
      rw [← Subgroup.index_ker d]
      exact d.ker.card_mul_index.symm
    _ ≤ Nat.card d.ker * Nat.card d.ker :=
      Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective
        (Subgroup.inclusion hrange) (Subgroup.inclusion_injective hrange))
    _ = (Nat.card {q : Q // f q = q}) ^ 2 := by rw [hkcard, pow_two]

end FiveTransitive.InvolutiveAutomorphismBound

end CFSG
