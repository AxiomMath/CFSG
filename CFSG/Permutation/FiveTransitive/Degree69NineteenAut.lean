module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree69NineteenAut

open MulAction

private theorem eq_one
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 19 Q)
    (hcard : Nat.card Q ≤ 19 ^ 2) (a : MulAut Q) (ha : a ^ 11 = 1) : a = 1 := by
  classical
  let _ : Fact (Nat.Prime 19) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let A := Subgroup.zpowers a
  have hA : IsPGroup 11 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one ha)
  let C := FixedPoints.subgroup A Q
  have hmod : Nat.card Q % 11 = Nat.card C % 11 := hA.card_modEq_card_fixedPoints Q
  have hle : Nat.card C ≤ Nat.card Q := Nat.card_le_card_of_injective
    (fun x : C => x.val) Subtype.val_injective
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨d,hd⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup C)
  have hbound (k : ℕ) (hk : 19 ^ k ≤ 19 ^ 2) : k ≤ 2 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 19) (by omega : 3 ≤ k)
    norm_num at hh hk
    omega
  have he4 := hbound e (he ▸ hcard)
  have hd4 := hbound d (hd ▸ hle.trans hcard)
  have hcards : Nat.card C = Nat.card Q := by
    rw [he,hd] at hmod ⊢
    interval_cases e <;> interval_cases d <;> norm_num at *
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C hcards
  apply MulEquiv.ext
  intro q
  exact (show q ∈ C from htop ▸ Subgroup.mem_top q) ⟨a,Subgroup.mem_zpowers a⟩

theorem centralizes
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 19 Q) (hQcard : Nat.card Q ≤ 19 ^ 2)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 11 = 1) :
    g.val ∈ Subgroup.centralizer (Q : Set G) := by
  have ha : Q.normalizerMonoidHom g = 1 :=
    eq_one hQ hQcard _ (by rw [← map_pow,hg,map_one])
  apply Subgroup.mem_centralizer_iff.mpr
  intro q hq
  have hh := congrArg (fun f : MulAut Q => (f ⟨q,hq⟩).val) ha
  rw [Q.normalizerMonoidHom_apply_apply_coe] at hh
  exact ((mul_inv_eq_iff_eq_mul).mp hh).symm

end FiveTransitive.Degree69NineteenAut

end CFSG
