module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

private theorem one_sub_sum_le_prod_multiset (s : Multiset R)
    (h0 : ∀ a ∈ s, 0 ≤ a) (h1 : ∀ a ∈ s, a ≤ 1) :
    1 - s.sum ≤ (s.map fun a => 1 - a).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons]
      have ha0 : 0 ≤ a := h0 a (by simp)
      have ha1 : a ≤ 1 := h1 a (by simp)
      have ht0 : ∀ b ∈ t, 0 ≤ b := fun b hb => h0 b (by simp [hb])
      have ht1 : ∀ b ∈ t, b ≤ 1 := fun b hb => h1 b (by simp [hb])
      have hsum0 : 0 ≤ t.sum := Multiset.sum_nonneg ht0
      have ih' := ih ht0 ht1
      have h1a : 0 ≤ 1 - a := sub_nonneg.mpr ha1
      have hquad : 1 - a - t.sum ≤ (1 - a) * (1 - t.sum) := by
        have hmul : 0 ≤ a * t.sum := mul_nonneg ha0 hsum0
        have h : (1 - a) * (1 - t.sum) = 1 - a - t.sum + a * t.sum := by ring
        rw [h]
        exact le_add_of_nonneg_right hmul
      calc 1 - (a + t.sum) = 1 - a - t.sum := by ring
        _ ≤ (1 - a) * (1 - t.sum) := hquad
        _ ≤ (1 - a) * (t.map fun a => 1 - a).prod :=
            mul_le_mul_of_nonneg_left ih' h1a

theorem one_sub_sum_le_prod_finset {ι : Type*} (s : Finset ι) (x : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  have h0' : ∀ a ∈ s.val.map x, 0 ≤ a := by
    intro a ha
    rcases Multiset.mem_map.mp ha with ⟨i, hi, rfl⟩
    exact h0 i (by simpa using hi)
  have h1' : ∀ a ∈ s.val.map x, a ≤ 1 := by
    intro a ha
    rcases Multiset.mem_map.mp ha with ⟨i, hi, rfl⟩
    exact h1 i (by simpa using hi)
  have h := one_sub_sum_le_prod_multiset (s.val.map x) h0' h1'
  rw [Finset.sum_eq_multiset_sum s x,
    Finset.prod_eq_multiset_prod s (fun i => 1 - x i)]
  simpa [Multiset.map_map, Function.comp_def] using h

end CFSG

end
