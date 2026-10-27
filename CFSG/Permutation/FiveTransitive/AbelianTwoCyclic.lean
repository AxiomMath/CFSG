module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.AbelianTwoCyclic

variable {A : Type*} [CommGroup A]

private theorem square_fiber_card_le [Fintype A] [DecidableEq A]
    (h : (Finset.univ.filter (fun a : A => a ^ 2 = 1)).card ≤ 2)
    (s : Finset A) (b : A) : (s.filter (fun a => a ^ 2 = b)).card ≤ 2 := by
  by_cases hn : (s.filter (fun a => a ^ 2 = b)).Nonempty
  · obtain ⟨c, hc⟩ := hn
    have hc2 : c ^ 2 = b := (Finset.mem_filter.mp hc).2
    apply le_trans (Finset.card_le_card_of_injOn (fun a : A => a * c⁻¹) ?_ ?_) h
    · intro a ha
      have ha2 : a ^ 2 = b := (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mul_pow, inv_pow, ha2, hc2, mul_inv_cancel]
    · intro a _ d _ had
      exact mul_right_cancel had
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty]
    exact Nat.zero_le 2

private theorem iterated_square_kernel_card_le [Fintype A] [DecidableEq A]
    (h : (Finset.univ.filter (fun a : A => a ^ 2 = 1)).card ≤ 2) (k : ℕ) :
    (Finset.univ.filter (fun a : A => a ^ (2 ^ k) = 1)).card ≤ 2 ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, pow_one]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  | succ k ih =>
    calc
      _ ≤ 2 * (Finset.univ.filter (fun a : A => a ^ (2 ^ k) = 1)).card := by
        refine Finset.card_le_mul_card_image_of_maps_to (f := fun a : A => a ^ 2) ?_ 2 ?_
        · intro a ha
          have ha2 := (Finset.mem_filter.mp ha).2
          apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← pow_mul, ← pow_succ' 2 k]
          exact ha2
        · intro b _
          exact square_fiber_card_le h _ b
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := (pow_succ' 2 k).symm

theorem isCyclic_of_square_kernel_card_le_two [Finite A] (hA : IsPGroup 2 A)
    (h : Nat.card {a : A // a ^ 2 = 1} ≤ 2) : IsCyclic A := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hs : (Finset.univ.filter (fun a : A => a ^ 2 = 1)).card ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  obtain ⟨a, ha⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := A))
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA a
  apply isCyclic_of_card_le_orderOf a
  have hall : ∀ a : A, a ^ (2 ^ k) = 1 := by
    intro b
    rw [← hk, ha]
    exact Monoid.pow_exponent_eq_one b
  have hb := iterated_square_kernel_card_le hs k
  have he : (Finset.univ.filter (fun a : A => a ^ (2 ^ k) = 1)) = Finset.univ := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, hall, and_self]
  rw [he, Finset.card_univ, ← Nat.card_eq_fintype_card, ← hk] at hb
  exact hb

end FiveTransitive.AbelianTwoCyclic

end CFSG
