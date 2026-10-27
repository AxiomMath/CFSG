module

public import CFSG.Sporadic.Ly.RREF
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Sporadic.Ly.Omega

open CFSG.Sporadic.Ly

section Generic

variable {G : Type*} [Group G]

theorem orderOf_eq_21 {u : G} (h21 : u ^ 21 = 1) (h7 : u ^ 7 ≠ 1) (h3 : u ^ 3 ≠ 1) :
    orderOf u = 21 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h21 fun p hp hpd => ?_
  have h21' : p ∣ 3 * 7 := hpd
  rcases (Nat.Prime.dvd_mul hp).1 h21' with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    exact h7
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    exact h3

theorem exists_gen_pair_of (a u z t : G) (hu : orderOf u = 21) (hau : a * u = u * a)
    (haz : a * z = z * a) (hut : u ^ 7 * t = t * u ^ 7)
    (hzt : Subgroup.closure ({z, t} : Set G) = ⊤) :
    ∃ u : G, orderOf u = 21 ∧ a * u = u * a ∧
      Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({u ^ 7} : Set G) = ⊤ := by
  refine ⟨u, hu, hau, ?_⟩
  rw [eq_top_iff, ← hzt, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.2 haz.symm)
  · exact Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.2 hut.symm)

end Generic

end CFSG.Sporadic.Ly.Omega
