module

public import CFSG.Permutation.FiveTransitive.TwoPowerModFive
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.TwoGroupFiveAutomorphism

open MulAction

theorem card_eq_sixteen_of_nontrivial_action
    (A Q : Type*) [Group A] [Group Q] [Finite Q]
    [MulDistribMulAction A Q]
    (hA : IsPGroup 5 A) (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (hmove : ∃ a : A, ∃ q : Q, a • q ≠ q) :
    Nat.card Q = 16 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C := FixedPoints.subgroup A Q
  have hCcard : Nat.card C = Nat.card (fixedPoints A Q) := rfl
  have hmod : Nat.card Q % 5 = Nat.card C % 5 := by
    have h := hA.card_modEq_card_fixedPoints Q
    change Nat.card Q % 5 = Nat.card (fixedPoints A Q) % 5 at h
    rwa [← hCcard] at h
  have hd : Nat.card C ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card C
  have hle : Nat.card C ≤ Nat.card Q := Nat.card_le_card_of_injective (fun x : C => (x : Q)) Subtype.val_injective
  have hlt : Nat.card C < Nat.card Q := lt_of_le_of_ne hle (by
    intro heq
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C heq
    obtain ⟨a,q,hq⟩ := hmove
    have hqC : q ∈ C := htop ▸ Subgroup.mem_top q
    exact hq (hqC a))
  exact TwoPowerModFive.eq_sixteen_of_proper_divisor (Nat.card Q) (Nat.card C)
    (IsPGroup.iff_card.mp hQ) hcard hd hlt hmod

theorem card_eq_sixteen_of_order_five
    (Q : Type*) [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (a : MulAut Q) (ha : orderOf a = 5) :
    Nat.card Q = 16 := by
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
  obtain ⟨q,hq⟩ := hmove
  apply card_eq_sixteen_of_nontrivial_action A Q hA hQ hcard
  exact ⟨⟨a, Subgroup.mem_zpowers a⟩, q, hq⟩

theorem card_eq_sixteen_of_five_dvd_aut_card
    (Q : Type*) [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (hfive : 5 ∣ Nat.card (MulAut Q)) :
    Nat.card Q = 16 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := MulAut Q) 5 hfive
  exact card_eq_sixteen_of_order_five Q hQ hcard a ha

end FiveTransitive.TwoGroupFiveAutomorphism

end CFSG
