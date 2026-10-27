module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)

theorem arithExcl_of_card {J : Type} [Group J] [Finite J] (a b c : ℕ)
    (hcard : Nat.card J = 2 ^ a * 3 ^ b * c) (hc : ∀ m : ℕ, m ∣ c → m % 7 = 1 → m = 1) :
    ArithExcl J := by
  intro m hm hcop h7
  have hcop2 : Nat.Coprime m (2 ^ a * 3 ^ b) := by
    have h2 : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
    have h3 : Nat.Coprime m 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2) (Nat.Coprime.pow_right b h3)
  rw [hcard] at hm
  exact hc m (hcop2.dvd_of_dvd_mul_left hm) h7

theorem arith_of_divisors (c : ℕ) (hc0 : c ≠ 0)
    (h : ∀ m ∈ Nat.divisors c, m % 7 = 1 → m = 1) : ∀ m : ℕ, m ∣ c → m % 7 = 1 → m = 1 :=
  fun m hm h7 => h m (Nat.mem_divisors.mpr ⟨hm, hc0⟩) h7

theorem arith_five : ∀ m : ℕ, m ∣ 5 → m % 7 = 1 → m = 1 :=
  arith_of_divisors 5 (by norm_num) (by decide +kernel)

theorem arith_thirty_five : ∀ m : ℕ, m ∣ 35 → m % 7 = 1 → m = 1 :=
  arith_of_divisors 35 (by norm_num) (by decide +kernel)

theorem arith_fifty_five : ∀ m : ℕ, m ∣ 55 → m % 7 = 1 → m = 1 :=
  arith_of_divisors 55 (by norm_num) (by decide +kernel)

theorem arith_385 : ∀ m : ℕ, m ∣ 385 → m % 7 = 1 → m = 1 :=
  arith_of_divisors 385 (by norm_num) (by decide +kernel)

theorem arith_9625 : ∀ m : ℕ, m ∣ 9625 → m % 7 = 1 → m = 1 :=
  arith_of_divisors 9625 (by norm_num) (by decide +kernel)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
