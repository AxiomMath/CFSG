module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.FiveGroup625CenterBounds

theorem card_bounds
    (Q : Type*) [Group Q] [Finite Q] (hQ : IsPGroup 5 Q)
    (hcard : Nat.card Q ≤ 625) (hnonabelian : ¬ IsMulCommutative Q) :
    Nat.card (Subgroup.center Q) ≤ 125 ∧ Nat.card (Q ⧸ Subgroup.center Q) ≤ 125 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases subsingleton_or_nontrivial Q with htriv | hnontriv
  · let _ := htriv
    exact (hnonabelian inferInstance).elim
  let _ := hnontriv
  let Z := Subgroup.center Q
  let _ : Nontrivial Z := hQ.center_nontrivial
  have hZnontriv : 1 < Nat.card Z := Finite.one_lt_card
  have hZle : Nat.card Z ≤ Nat.card Q := Nat.card_le_card_of_injective
    Z.subtype Subtype.val_injective
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup Z)
  have hepos : 1 ≤ e := by
    by_contra hn
    have he0 : e = 0 := by omega
    rw [he,he0,pow_zero] at hZnontriv
    omega
  have he3 : e ≤ 3 := by
    by_contra hn
    have h625 := Nat.pow_le_pow_right (by norm_num : 0 < 5) (by omega : 4 ≤ e)
    change 625 ≤ 5 ^ e at h625
    rw [← he] at h625
    have hZe : Nat.card Z = Nat.card Q := by omega
    have htop : Z = ⊤ := Subgroup.eq_top_of_card_eq Z hZe
    exact hnonabelian (Subgroup.center_eq_top_iff.mp htop)
  have hZ125 : Nat.card Z ≤ 125 := by
    rw [he]
    exact (Nat.pow_le_pow_right (by norm_num : 0 < 5) he3).trans (by norm_num)
  have hZ5 : 5 ≤ Nat.card Z := by
    rw [he]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 5) hepos
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hmul := Nat.mul_le_mul_left (Nat.card (Q ⧸ Z)) hZ5
  rw [← hprod] at hmul
  have hV125 : Nat.card (Q ⧸ Z) ≤ 125 := by omega
  exact ⟨hZ125,hV125⟩

end FiveTransitive.FiveGroup625CenterBounds

end CFSG
