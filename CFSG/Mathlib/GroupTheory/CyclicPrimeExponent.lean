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
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard]; exact IsCyclic.card_pow_eq_one_le hp.pos)
  rw [heq]
  simpa using hb

end CFSG.GroupTheory
