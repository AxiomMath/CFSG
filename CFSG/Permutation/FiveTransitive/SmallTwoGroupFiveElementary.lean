module

public import CFSG.Permutation.FiveTransitive.SmallTwoGroupFiveElementaryAction

public section

namespace CFSG

namespace FiveTransitive.SmallTwoGroupFiveElementary

open MulAction

private theorem of_order_five
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (a : MulAut Q) (ha : orderOf a = 5) :
    Nat.card Q = 16 ∧ IsMulCommutative Q ∧ ∀ q : Q, q ^ 2 = 1 := by
  classical
  let A := Subgroup.zpowers a
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hA : IsPGroup 5 A := IsPGroup.iff_card.mpr ⟨1, by
    change Nat.card (Subgroup.zpowers a) = 5 ^ 1
    rw [Nat.card_zpowers, ha, pow_one]⟩
  have hane : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; omega
  have hmove : ∃ q : Q, a q ≠ q := by
    by_contra h
    push Not at h
    exact hane (by ext q; exact h q)
  obtain ⟨q, hq⟩ := hmove
  apply SmallTwoGroupFiveElementaryAction.elementary hA hQ hcard
  exact ⟨⟨a, Subgroup.mem_zpowers a⟩, q, hq⟩

theorem of_five_dvd_aut_card
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (hfive : 5 ∣ Nat.card (MulAut Q)) :
    Nat.card Q = 16 ∧ IsMulCommutative Q ∧ ∀ q : Q, q ^ 2 = 1 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := MulAut Q) 5 hfive
  exact of_order_five hQ hcard a ha

end FiveTransitive.SmallTwoGroupFiveElementary

end CFSG
