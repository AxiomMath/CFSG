module

public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.Vol2.Ch11SecB23Core

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem even_of_three_dvd {n : ℕ} (h : 3 ∣ 2 ^ n - 1) : Even n := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨k, rfl⟩ := hodd
  have h4 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; ring
  have hmod : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [h4, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpos : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * k + 1) = N at h hmod hpos
  omega

theorem dvd_two_pow_two_mul {p n : ℕ} (h : p ∣ 2 ^ n - 1) : p ∣ 2 ^ (2 * n) - 1 := by
  refine h.trans ⟨2 ^ n + 1, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ n = c + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  rw [pow_mul', hc, show (c + 1) ^ 2 = c * (c + 1 + 1) + 1 by ring, Nat.add_sub_cancel,
    Nat.add_sub_cancel]

end CFSG.Quasithin.Vol2.Ch11.SecE
