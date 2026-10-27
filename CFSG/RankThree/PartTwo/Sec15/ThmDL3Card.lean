module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open Subgroup

theorem card_inf_eq_nine {M : Type*} [Group M] [Finite M] (A Y : Subgroup M) [Y.Normal]
    (hA27 : Nat.card A = 27) (c : M) (hc : c ∈ A) (hcY : c ∉ Y) (hc3 : c ^ 3 = 1)
    (hAdec : ∀ a ∈ A, ∃ a₁ ∈ A ⊓ Y, ∃ i : ℕ, a = a₁ * c ^ i) :
    Nat.card (A ⊓ Y : Subgroup M) = 9 := by
  obtain ⟨f, hf⟩ : ∃ f : A →* M ⧸ Y, ∀ a : A, f a = QuotientGroup.mk' Y (a : M) :=
    ⟨(QuotientGroup.mk' Y).comp A.subtype, fun a => rfl⟩
  have hmk1 : ∀ y ∈ Y, QuotientGroup.mk' Y y = 1 := fun y hy =>
    (QuotientGroup.eq_one_iff y).2 hy
  have hmkc : QuotientGroup.mk' Y c ≠ 1 := fun h => hcY ((QuotientGroup.eq_one_iff c).1 h)
  have hmk3 : QuotientGroup.mk' Y c ^ 3 = 1 := by
    rw [← map_pow, hc3, map_one]
  have hrange : f.range = Subgroup.zpowers (QuotientGroup.mk' Y c) := by
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      obtain ⟨a₁, ha₁, i, hi⟩ := hAdec (a : M) a.2
      rw [hf, hi, map_mul, map_pow, hmk1 a₁ (Subgroup.mem_inf.mp ha₁).2, one_mul]
      exact pow_mem (Subgroup.mem_zpowers _) i
    · rw [Subgroup.zpowers_le]
      exact MonoidHom.mem_range.mpr ⟨⟨c, hc⟩, hf ⟨c, hc⟩⟩
  have hord : orderOf (QuotientGroup.mk' Y c) = 3 := orderOf_eq_prime hmk3 hmkc
  have hfr : Nat.card f.range = 3 := by
    have hfin : IsOfFinOrder (QuotientGroup.mk' Y c) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hmk3⟩
    rw [hrange, ← Nat.card_congr (finEquivZPowers hfin), Nat.card_fin, hord]
  have hk : f.ker = (A ⊓ Y).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, hf, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact Subgroup.mem_inf.mpr ⟨x.2, (QuotientGroup.eq_one_iff (x : M)).1 h⟩
    · intro h
      exact (QuotientGroup.eq_one_iff (x : M)).2 (Subgroup.mem_inf.mp h).2
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hfr, hA27] at hcard
  have hker9 : Nat.card f.ker = 9 := by omega
  rw [hk] at hker9
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ Y ≤ A)).toEquiv).symm.trans
    hker9

end CFSG.RankThree.PartTwo.Sec15.ThmD
