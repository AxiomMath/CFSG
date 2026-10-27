module

public import CFSG.CharacterTheory.Burnside
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

theorem isSolvable_of_card_two_three {G : Type} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h])

theorem exists_pow_two_pow_three_of_dvd {d : ℕ} (h : d ∣ 864) : ∃ a b : ℕ, d = 2 ^ a * 3 ^ b := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.1 (show d ∣ 2 ^ 5 * 3 ^ 3 from h)
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  exact ⟨a, b, rfl⟩

theorem card_sylow_seven_of_dvd {G : Type} [Group G] [Finite G] (h7 : 7 ∣ Nat.card G)
    (h6048 : Nat.card G ∣ 6048) (P : Sylow 7 G) : Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  have hd7 : 7 ∣ Nat.card P := P.dvd_card_of_dvd_card h7
  have hdvd : Nat.card P ∣ 6048 := (Subgroup.card_subgroup_dvd_card (P : Subgroup G)).trans h6048
  rw [hk] at hd7 hdvd ⊢
  have hk1 : k ≠ 0 := by
    rintro rfl
    norm_num at hd7
  have hk2 : k < 2 := by
    by_contra h
    have : 7 ^ 2 ∣ 6048 := (pow_dvd_pow 7 (by omega)).trans hdvd
    norm_num at this
  have : k = 1 := by omega
  rw [this, pow_one]

theorem sylow_seven_count_cases' {n : ℕ} (hdvd : n ∣ 288) (hmod : n % 7 = 1) :
    n = 1 ∨ n = 8 ∨ n = 36 ∨ n = 288 := by
  have key : ∀ m ∈ Nat.divisors 288, m % 7 = 1 → m = 1 ∨ m = 8 ∨ m = 36 ∨ m = 288 := by
    decide +kernel
  exact key n (Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩) hmod

end CFSG.Quasithin.H13.U3.GC137.SQ
