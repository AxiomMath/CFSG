module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.FiveSevenSmallAut

open MulAction

private theorem smul_eq
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : (p = 5 ∧ q = 7) ∨ (p = 7 ∧ q = 5))
    {A H : Type*} [Group A] [Group H] [Finite H] [MulDistribMulAction A H]
    (hA : IsPGroup q A) (hH : IsPGroup p H) (hcard : Nat.card H ≤ p ^ 2)
    (a : A) (h : H) : a • h = h := by
  classical
  let C := FixedPoints.subgroup A H
  have hmod : Nat.card H % q = Nat.card C % q := hA.card_modEq_card_fixedPoints H
  have hle : Nat.card C ≤ Nat.card H := Nat.card_le_card_of_injective
    (fun x : C => x.val) Subtype.val_injective
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hH
  obtain ⟨d,hd⟩ := IsPGroup.iff_card.mp (hH.to_subgroup C)
  have hbound (k : ℕ) (hk : p ^ k ≤ p ^ 2) : k ≤ 2 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : 3 ≤ k)
    have h23 : p ^ 2 < p ^ 3 := by
      rcases hpq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
    omega
  have he2 := hbound e (he ▸ hcard)
  have hd2 := hbound d (hd ▸ hle.trans hcard)
  have hsame : Nat.card C = Nat.card H := by
    rw [he,hd] at hmod ⊢
    rcases hpq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      interval_cases e <;> interval_cases d <;> norm_num at *
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C hsame
  have hh : h ∈ C := htop ▸ Subgroup.mem_top h
  exact hh a

theorem eq_one
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : (p = 5 ∧ q = 7) ∨ (p = 7 ∧ q = 5))
    (H : Type*) [Group H] [Finite H]
    (hH : IsPGroup p H) (hcard : Nat.card H ≤ p ^ 2)
    (f : MulAut H) (hf : f ^ q = 1) : f = 1 := by
  have hA : IsPGroup q (Subgroup.zpowers f) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hf)
  ext h
  exact smul_eq hpq hA hH hcard (⟨f,Subgroup.mem_zpowers f⟩ : Subgroup.zpowers f) h

end FiveTransitive.FiveSevenSmallAut

end CFSG
