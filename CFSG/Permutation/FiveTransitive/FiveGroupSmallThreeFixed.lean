module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.FiveGroupSmallThreeFixed

open MulAction

theorem card_and_fixed
    {A Q : Type*} [Group A] [Group Q] [Finite Q] [MulDistribMulAction A Q]
    (hA : IsPGroup 3 A) (hQ : IsPGroup 5 Q) (hcard : Nat.card Q ≤ 125)
    (hmove : ∃ a : A, ∃ q : Q, a • q ≠ q) :
    (Nat.card Q = 25 ∧ Nat.card (FixedPoints.subgroup A Q) = 1) ∨
      (Nat.card Q = 125 ∧ Nat.card (FixedPoints.subgroup A Q) = 5) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C := FixedPoints.subgroup A Q
  have hmod : Nat.card Q % 3 = Nat.card C % 3 := hA.card_modEq_card_fixedPoints Q
  have hle : Nat.card C ≤ Nat.card Q := Nat.card_le_card_of_injective
    (fun x : C => x.val) Subtype.val_injective
  have hlt : Nat.card C < Nat.card Q := lt_of_le_of_ne hle (by
    intro he
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C he
    obtain ⟨a,q,hq⟩ := hmove
    exact hq ((show q ∈ C from htop ▸ Subgroup.mem_top q) a))
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨d,hd⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup C)
  have hbound (k : ℕ) (hk : 5 ^ k ≤ 125) : k ≤ 3 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 5) (by omega : 4 ≤ k)
    norm_num at hh
    omega
  have he4 := hbound e (he ▸ hcard)
  have hd4 := hbound d (hd ▸ hle.trans hcard)
  rw [he,hd] at hmod hlt ⊢
  interval_cases e <;> interval_cases d <;> norm_num at *

end FiveTransitive.FiveGroupSmallThreeFixed

end CFSG
