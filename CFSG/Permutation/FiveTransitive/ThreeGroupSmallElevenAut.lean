module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.ThreeGroupSmallElevenAut

open MulAction

private theorem smul_eq
    {A Q : Type*} [Group A] [Group Q] [Finite Q] [MulDistribMulAction A Q]
    (hA : IsPGroup 11 A) (hQ : IsPGroup 3 Q) (hcard : Nat.card Q ≤ 81)
    (a : A) (q : Q) : a • q = q := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let C := FixedPoints.subgroup A Q
  have hmod : Nat.card Q % 11 = Nat.card C % 11 := hA.card_modEq_card_fixedPoints Q
  have hle : Nat.card C ≤ Nat.card Q := Nat.card_le_card_of_injective
    (fun x : C => x.val) Subtype.val_injective
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨d,hd⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup C)
  have hbound (k : ℕ) (hk : 3 ^ k ≤ 81) : k ≤ 4 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 5 ≤ k)
    norm_num at hh
    omega
  have he4 := hbound e (he ▸ hcard)
  have hd4 := hbound d (hd ▸ hle.trans hcard)
  have hsame : Nat.card C = Nat.card Q := by
    rw [he,hd] at hmod ⊢
    interval_cases e <;> interval_cases d <;> norm_num at *
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C hsame
  have hq : q ∈ C := htop ▸ Subgroup.mem_top q
  exact hq a

theorem eq_one
    (Q : Type*) [Group Q] [Finite Q]
    (hQ : IsPGroup 3 Q) (hcard : Nat.card Q ≤ 81)
    (f : MulAut Q) (hf : f ^ 11 = 1) : f = 1 := by
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hA : IsPGroup 11 (Subgroup.zpowers f) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hf)
  ext q
  exact smul_eq hA hQ hcard (⟨f,Subgroup.mem_zpowers f⟩ : Subgroup.zpowers f) q

end FiveTransitive.ThreeGroupSmallElevenAut

end CFSG
