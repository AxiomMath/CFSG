module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG

namespace FiveTransitive.ExponentTwoDisplacement

private theorem exists_displacement_of_card_eq_square
    (Q : Type*) [CommGroup Q] [Finite Q]
    (f : Q →* Q) (hf : Function.Involutive f)
    (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = (Nat.card {q : Q // f q = q}) ^ 2)
    (x : Q) (hx : f x = x) : ∃ q : Q, f q * q = x := by
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
    rintro q ⟨r, rfl⟩
    rw [hker, hd, map_mul, hf]
    exact mul_comm _ _
  have hkcard : Nat.card d.ker = Nat.card {q : Q // f q = q} :=
    Nat.card_congr
      { toFun := fun q => ⟨q, (hker q).mp q.property⟩
        invFun := fun q => ⟨q, (hker q).mpr q.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hprod : Nat.card Q = Nat.card d.ker * Nat.card d.range := by
    rw [← Subgroup.index_ker d]
    exact d.ker.card_mul_index.symm
  have heqcard : Nat.card d.range = Nat.card d.ker := by
    rw [hcard, ← hkcard, pow_two] at hprod
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hprod).symm
  have heq : d.range = d.ker := Subgroup.eq_of_le_of_card_ge hrange heqcard.ge
  have hxrange : x ∈ d.range := heq.symm ▸ (hker x).mpr hx
  exact hxrange

theorem exists_displacement_of_sixteen_four
    (Q : Type*) [CommGroup Q] [Finite Q]
    (f : Q →* Q) (hf : Function.Involutive f)
    (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = 16) (hfix : Nat.card {q : Q // f q = q} = 4)
    (x : Q) (hx : f x = x) : ∃ q : Q, f q * q = x := by
  apply exists_displacement_of_card_eq_square Q f hf h2 _ x hx
  rw [hcard, hfix]
  rfl

end FiveTransitive.ExponentTwoDisplacement

end CFSG
