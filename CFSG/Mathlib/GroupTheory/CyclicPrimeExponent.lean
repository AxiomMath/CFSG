module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GroupTheory

theorem mem_zpowers_of_pow_eq_one_of_prime {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} (hp : p.Prime) {a b : G} (ha : a ^ p = 1) (ha1 : a ≠ 1) (hb : b ^ p = 1) :
    b ∈ Subgroup.zpowers a := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have : Fact p.Prime := ⟨hp⟩
  have hoa : orderOf a = p := orderOf_eq_prime ha ha1
  rw [mem_zpowers_iff_mem_range_orderOf, hoa]
  have hbound : (Finset.univ.filter fun x : G => x ^ p = 1).card ≤ p := by
    obtain ⟨g, hsurj⟩ := exists_zpow_surjective G
    have hg : ∀ x : G, x ∈ Subgroup.zpowers g := fun x => by
      obtain ⟨k, hk⟩ := hsurj x
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩
    have hgen : ∀ x : G, x ∈ Submonoid.powers g := fun x =>
      mem_powers_iff_mem_zpowers.mpr (hg x)
    have hord : orderOf g = Nat.card G := by
      rw [← Fintype.card_zpowers (x := g), ← Nat.card_eq_fintype_card,
        (Subgroup.eq_top_iff' _).mpr hg, Subgroup.card_top]
    calc (Finset.univ.filter fun x : G => x ^ p = 1).card
        ≤ ((Subgroup.zpowers (g ^ (Fintype.card G / Nat.gcd p (Fintype.card G))) :
                Set G)).toFinset.card := by
          refine Finset.card_le_card fun x hx => ?_
          rw [Set.mem_toFinset]
          obtain ⟨m, hm⟩ := hgen x
          refine Subgroup.mem_zpowers_iff.mpr
            ⟨(m / (Fintype.card G / Nat.gcd p (Fintype.card G)) : ℕ), ?_⟩
          dsimp only at ⊢ hm
          rw [zpow_natCast, ← pow_mul, Nat.mul_div_cancel_left', hm]
          refine Nat.dvd_of_mul_dvd_mul_right (Nat.gcd_pos_of_pos_left (Fintype.card G) hp.pos) ?_
          conv_lhs =>
            rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), ← Nat.card_eq_fintype_card, ← hord]
          exact orderOf_dvd_of_pow_eq_one <|
            by simpa [pow_mul, hm] using (Finset.mem_filter.1 hx).2
      _ ≤ p := by
          let ⟨m, hm⟩ := Nat.gcd_dvd_right p (Fintype.card G)
          have hm0 : 0 < m :=
            Nat.pos_of_ne_zero fun hm0 => by
              rw [hm0, mul_zero, Fintype.card_eq_zero_iff] at hm
              exact hm.elim' 1
          simp only [Set.toFinset_card, SetLike.coe_sort_coe]
          rw [Fintype.card_zpowers, orderOf_pow g, hord, Nat.card_eq_fintype_card]
          nth_rw 2 [hm]; nth_rw 3 [hm]
          rw [Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ hp.pos), Nat.gcd_mul_left_left, hm,
            Nat.mul_div_cancel _ hm0]
          exact Nat.le_of_dvd hp.pos (Nat.gcd_dvd_left _ _)
  have hsub : (Finset.range p).image (a ^ ·) ⊆ Finset.univ.filter fun x : G => x ^ p = 1 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter, ← pow_mul, mul_comm, pow_mul, ha, one_pow]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hcard : ((Finset.range p).image (a ^ ·)).card = p := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by rw [hoa]; exact Finset.mem_range.mp hi)
      (by rw [hoa]; exact Finset.mem_range.mp hj) hij
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hbound)
  rw [heq]
  simpa using hb

end CFSG.GroupTheory
