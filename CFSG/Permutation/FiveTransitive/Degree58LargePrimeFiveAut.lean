module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree58LargePrimeFiveAut

open MulAction

theorem eq_one
    (p : ℕ) (hp : p.Prime) (hcases : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup p Q)
    (hcard : Nat.card Q ≤ if p = 19 then 19 else p ^ 2)
    (a : MulAut Q) (ha : a ^ 5 = 1) : a = 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A := Subgroup.zpowers a
  have hA : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one ha)
  let C := FixedPoints.subgroup A Q
  have hmod : Nat.card Q % 5 = Nat.card C % 5 := hA.card_modEq_card_fixedPoints Q
  have hle : Nat.card C ≤ Nat.card Q := Nat.card_le_card_of_injective
    (fun x : C => x.val) Subtype.val_injective
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨d,hd⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup C)
  have hbound (k : ℕ) (hk : p ^ k ≤ if p = 19 then 19 else p ^ 2) : k ≤ 2 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right hp.pos (by omega : 3 ≤ k)
    rcases hcases with rfl | rfl | rfl | rfl <;> norm_num at hk hh <;> omega
  have he2 := hbound e (he ▸ hcard)
  have hd2 := hbound d (hd ▸ hle.trans hcard)
  have hcards : Nat.card C = Nat.card Q := by
    rw [he,hd] at hmod hle ⊢
    rw [he] at hcard
    interval_cases e <;> interval_cases d <;>
      rcases hcases with rfl | rfl | rfl | rfl <;> norm_num at *
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C hcards
  apply MulEquiv.ext
  intro q
  exact (show q ∈ C from htop ▸ Subgroup.mem_top q) ⟨a,Subgroup.mem_zpowers a⟩

end FiveTransitive.Degree58LargePrimeFiveAut

end CFSG
