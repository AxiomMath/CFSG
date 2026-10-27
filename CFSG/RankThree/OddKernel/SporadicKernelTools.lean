module

public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.RankThree.OddKernel

open CFSG.SectionRank

section Restriction

variable {E S : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group S] [Finite S]

theorem sq_dvd_card_of_prime_dvd_card_ker (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r ^ 2 ∣ Nat.card S := by
  have : Fact r.Prime := ⟨hr⟩
  by_contra hsq
  obtain ⟨Cp⟩ : Nonempty (Sylow r π.ker) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow r S) := inferInstance
  exact Cp.ne_bot_of_dvd_card hrC
    (CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cp Q
      (sylow_isCyclic_of_not_sq_dvd hsq Q))

theorem prime_dvd_card_ker_props (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6) {r : ℕ}
    (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) : r ≠ 2 ∧ r ≠ 3 ∧ r ^ 2 ∣ Nat.card S := by
  refine ⟨?_, ?_, sq_dvd_card_of_prime_dvd_card_ker π hπ hC hr hrC⟩
  · rintro rfl
    have h := Nat.Coprime.coprime_dvd_left hrC h6
    norm_num at h
  · rintro rfl
    have h := Nat.Coprime.coprime_dvd_left hrC h6
    norm_num at h

theorem prime_mem_of_card_eq (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6) {N : ℕ}
    (hS : Nat.card S = N) {P : ℕ → Prop}
    (hN : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ^ 2 ∣ N → P r) {r : ℕ} (hr : r.Prime)
    (hrC : r ∣ Nat.card π.ker) : P r := by
  obtain ⟨hr2, hr3, hsq⟩ := prime_dvd_card_ker_props π hπ hC h6 hr hrC
  exact hN r hr hr2 hr3 (hS ▸ hsq)

theorem eq_bot_of_forall_prime_not_dvd {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (h : ∀ r : ℕ, r.Prime → ¬ r ∣ Nat.card K) : K = ⊥ := by
  rw [← Subgroup.card_eq_one]
  by_contra h1
  obtain ⟨r, hr, hrK⟩ := Nat.exists_prime_and_dvd h1
  exact h r hr hrK

theorem ker_eq_bot_of_card_eq (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6) {N : ℕ}
    (hS : Nat.card S = N) (hN : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ N) :
    π.ker = ⊥ :=
  eq_bot_of_forall_prime_not_dvd _ fun _ hr hrC =>
    prime_mem_of_card_eq π hπ hC h6 hS (P := fun _ => False) (fun r hr h2 h3 h => hN r hr h2 h3 h)
      hr hrC

end Restriction

section Arithmetic

theorem coprime_two_three_pow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (a b : ℕ) :
    Nat.Coprime r (2 ^ a * 3 ^ b) :=
  Nat.Coprime.mul_right (coprime_pow_of_ne hr Nat.prime_two hr2 a)
    (coprime_pow_of_ne hr Nat.prime_three hr3 b)

theorem coprime_two_three_five_pow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hr5 : r ≠ 5) (a b c : ℕ) : Nat.Coprime r (2 ^ a * 3 ^ b * 5 ^ c) :=
  Nat.Coprime.mul_right (coprime_two_three_pow hr hr2 hr3 a b)
    (coprime_pow_of_ne hr (by norm_num) hr5 c)

theorem coprime_two_three_seven_pow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hr7 : r ≠ 7) (a b d : ℕ) : Nat.Coprime r (2 ^ a * 3 ^ b * 7 ^ d) :=
  Nat.Coprime.mul_right (coprime_two_three_pow hr hr2 hr3 a b)
    (coprime_pow_of_ne hr (by norm_num) hr7 d)

theorem coprime_two_three_five_seven_pow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hr5 : r ≠ 5) (hr7 : r ≠ 7) (a b c d : ℕ) : Nat.Coprime r (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :=
  Nat.Coprime.mul_right (coprime_two_three_five_pow hr hr2 hr3 hr5 a b c)
    (coprime_pow_of_ne hr (by norm_num) hr7 d)

theorem sq_primes_J3 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    ¬ r ^ 2 ∣ 50232960 := by
  rw [show 50232960 = (2 ^ 7 * 3 ^ 5) * [5, 17, 19].prod by norm_num]
  exact not_sq_dvd_of_factorization hr (coprime_two_three_pow hr hr2 hr3 _ _) _ (by norm_num)
    (by decide)

theorem sq_primes_Co1 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 4157776806543360000) : r = 5 ∨ r = 7 := by
  by_contra hne
  push Not at hne
  rw [show 4157776806543360000 = (2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2) * [11, 13, 23].prod by
    norm_num] at h
  exact not_sq_dvd_of_factorization hr
    (coprime_two_three_five_seven_pow hr hr2 hr3 hne.1 hne.2 _ _ _ _) _ (by norm_num) (by decide) h

theorem sq_primes_Fi24prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 1255205709190661721292800) : r = 5 ∨ r = 7 := by
  by_contra hne
  push Not at hne
  rw [show 1255205709190661721292800 =
    (2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3) * [11, 13, 17, 23, 29].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr
    (coprime_two_three_five_seven_pow hr hr2 hr3 hne.1 hne.2 _ _ _ _) _ (by norm_num) (by decide) h

theorem sq_primes_Th {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 90745943887872000) : r = 5 ∨ r = 7 := by
  by_contra hne
  push Not at hne
  rw [show 90745943887872000 = (2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2) * [13, 19, 31].prod by
    norm_num] at h
  exact not_sq_dvd_of_factorization hr
    (coprime_two_three_five_seven_pow hr hr2 hr3 hne.1 hne.2 _ _ _ _) _ (by norm_num) (by decide) h

theorem sq_primes_B {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 4154781481226426191177580544000000) : r = 5 ∨ r = 7 := by
  by_contra hne
  push Not at hne
  rw [show 4154781481226426191177580544000000 =
    (2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2) * [11, 13, 17, 19, 23, 31, 47].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr
    (coprime_two_three_five_seven_pow hr hr2 hr3 hne.1 hne.2 _ _ _ _) _ (by norm_num) (by decide) h

theorem sq_primes_Co2 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 42305421312000) : r = 5 := by
  by_contra hne
  rw [show 42305421312000 = (2 ^ 18 * 3 ^ 6 * 5 ^ 3) * [7, 11, 23].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_five_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

theorem sq_primes_Co3 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 495766656000) : r = 5 := by
  by_contra hne
  rw [show 495766656000 = (2 ^ 10 * 3 ^ 7 * 5 ^ 3) * [7, 11, 23].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_five_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

theorem sq_primes_Fi22 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 64561751654400) : r = 5 := by
  by_contra hne
  rw [show 64561751654400 = (2 ^ 17 * 3 ^ 9 * 5 ^ 2) * [7, 11, 13].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_five_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

theorem sq_primes_Fi23 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 4089470473293004800) : r = 5 := by
  by_contra hne
  rw [show 4089470473293004800 = (2 ^ 18 * 3 ^ 13 * 5 ^ 2) * [7, 11, 13, 17, 23].prod by
    norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_five_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

theorem sq_primes_McL {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 898128000) : r = 5 := by
  by_contra hne
  rw [show 898128000 = (2 ^ 7 * 3 ^ 6 * 5 ^ 3) * [7, 11].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_five_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

theorem sq_primes_Suz {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 448345497600) : r = 5 := by
  by_contra hne
  rw [show 448345497600 = (2 ^ 13 * 3 ^ 7 * 5 ^ 2) * [7, 11, 13].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_five_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

theorem sq_primes_HN {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 273030912000000) : r = 5 := by
  by_contra hne
  rw [show 273030912000000 = (2 ^ 14 * 3 ^ 6 * 5 ^ 6) * [7, 11, 19].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_five_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

theorem sq_primes_Ly {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 51765179004000000) : r = 5 := by
  by_contra hne
  rw [show 51765179004000000 = (2 ^ 8 * 3 ^ 7 * 5 ^ 6) * [7, 11, 31, 37, 67].prod by
    norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_five_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

theorem sq_primes_ON {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ 2 ∣ 460815505920) : r = 7 := by
  by_contra hne
  rw [show 460815505920 = (2 ^ 9 * 3 ^ 4 * 7 ^ 3) * [5, 11, 19, 31].prod by norm_num] at h
  exact not_sq_dvd_of_factorization hr (coprime_two_three_seven_pow hr hr2 hr3 hne _ _ _) _
    (by norm_num) (by decide) h

end Arithmetic

end CFSG.RankThree.OddKernel
