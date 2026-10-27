module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG

namespace FiveTransitive.Degree48SevenAut

open MulAction

theorem smul_eq
    {A H : Type*} [Group A] [Group H] [Finite H] [MulDistribMulAction A H]
    (hA : IsPGroup 5 A) (hH : IsPGroup 7 H) (hcard : Nat.card H ≤ 343)
    (a : A) (h : H) : a • h = h := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let C := FixedPoints.subgroup A H
  have hmod : Nat.card H % 5 = Nat.card C % 5 := hA.card_modEq_card_fixedPoints H
  have hle : Nat.card C ≤ Nat.card H := Nat.card_le_card_of_injective
    (fun x : C => x.val) Subtype.val_injective
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hH
  obtain ⟨d,hd⟩ := IsPGroup.iff_card.mp (hH.to_subgroup C)
  have hbound (k : ℕ) (hk : 7 ^ k ≤ 343) : k ≤ 3 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 7) (by omega : 4 ≤ k)
    change 2401 ≤ 7 ^ k at hh
    omega
  have he3 := hbound e (he ▸ hcard)
  have hd3 := hbound d (hd ▸ hle.trans hcard)
  have hsame : Nat.card C = Nat.card H := by
    rw [he,hd] at hmod ⊢
    interval_cases e <;> interval_cases d <;> norm_num at *
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C hsame
  have hh : h ∈ C := htop ▸ Subgroup.mem_top h
  exact hh a

theorem eq_one
    (H : Type*) [Group H] [Finite H]
    (hH : IsPGroup 7 H) (hcard : Nat.card H ≤ 343)
    (f : MulAut H) (hf : f ^ 5 = 1) : f = 1 := by
  have hA : IsPGroup 5 (Subgroup.zpowers f) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hf)
  ext h
  exact smul_eq hA hH hcard (⟨f,Subgroup.mem_zpowers f⟩ : Subgroup.zpowers f) h

end FiveTransitive.Degree48SevenAut

end CFSG
