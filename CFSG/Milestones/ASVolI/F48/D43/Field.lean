module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs

public section

namespace CFSG.ASVolI

section Codes

variable {K : Type*} [Field K] [CharP K 3] (ω : K)

@[expose] def burnsideF48d_φ (n : ℕ) : K :=
  ((n % 3 : ℕ) : K) + ((n / 3 % 3 : ℕ) : K) * ω + ((n / 9 % 3 : ℕ) : K) * ω ^ 2

omit [CharP K 3] in
theorem burnsideF48d_φ_digits {d0 d1 d2 : ℕ} (h0 : d0 < 3) (h1 : d1 < 3) (h2 : d2 < 3) :
    burnsideF48d_φ ω (d0 + 3 * d1 + 9 * d2) = (d0 : K) + (d1 : K) * ω + (d2 : K) * ω ^ 2 := by
  unfold burnsideF48d_φ
  rw [show (d0 + 3 * d1 + 9 * d2) % 3 = d0 by omega, show (d0 + 3 * d1 + 9 * d2) / 3 % 3 = d1 by omega,
    show (d0 + 3 * d1 + 9 * d2) / 9 % 3 = d2 by omega]

theorem burnsideF48d_cast_mod (n : ℕ) : ((n % 3 : ℕ) : K) = (n : K) :=
  (CharP.cast_eq_mod K 3 n).symm

theorem burnsideF48d_φ_add (a b : ℕ) :
    burnsideF48d_φ ω (burnsideF48d_addC a b) = burnsideF48d_φ ω a + burnsideF48d_φ ω b := by
  unfold burnsideF48d_addC
  rw [burnsideF48d_φ_digits ω (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))]
  simp only [burnsideF48d_φ, burnsideF48d_cast_mod, Nat.cast_add]
  ring

theorem burnsideF48d_φ_mul (hω : ω ^ 3 = ω + 1) (a b : ℕ) :
    burnsideF48d_φ ω (burnsideF48d_mulC a b) = burnsideF48d_φ ω a * burnsideF48d_φ ω b := by
  unfold burnsideF48d_mulC
  rw [burnsideF48d_φ_digits ω (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))]
  simp only [burnsideF48d_φ]
  generalize a % 3 = a0
  generalize a / 3 % 3 = a1
  generalize a / 9 % 3 = a2
  generalize b % 3 = b0
  generalize b / 3 % 3 = b1
  generalize b / 9 % 3 = b2
  simp only [burnsideF48d_cast_mod, Nat.cast_add, Nat.cast_mul]
  linear_combination (-((a1 : K) * (b2 : K) + (a2 : K) * (b1 : K) + (a2 : K) * (b2 : K) * ω)) * hω

theorem burnsideF48d_φ_frob (hω : ω ^ 3 = ω + 1) (a : ℕ) :
    burnsideF48d_φ ω (burnsideF48d_frobC a) = burnsideF48d_φ ω a ^ 3 := by
  rw [burnsideF48d_frobC, burnsideF48d_φ_mul ω hω, burnsideF48d_φ_mul ω hω]
  ring

theorem burnsideF48d_φ_pow (hω : ω ^ 3 = ω + 1) (a k : ℕ) :
    burnsideF48d_φ ω (burnsideF48d_powC a k) = burnsideF48d_φ ω a ^ k := by
  induction k with
  | zero =>
    simp [burnsideF48d_powC, burnsideF48d_φ]
  | succ k ih =>
    rw [burnsideF48d_powC, burnsideF48d_φ_mul ω hω, ih, pow_succ, mul_comm]

theorem burnsideF48d_φ_zero : burnsideF48d_φ ω 0 = 0 := by simp [burnsideF48d_φ]

theorem burnsideF48d_φ_one : burnsideF48d_φ ω 1 = 1 := by simp [burnsideF48d_φ]

theorem burnsideF48d_φ_three : burnsideF48d_φ ω 3 = ω := by simp [burnsideF48d_φ]

theorem burnsideF48d_φ_intC (z : ℤ) : burnsideF48d_φ ω (burnsideF48d_intC z) = (z : K) := by
  have h3 : ((3 : ℤ) : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hr : (0 : ℤ) ≤ z % (3 : ℤ) := Int.emod_nonneg z (by norm_num)
  have hlt : z % (3 : ℤ) < 3 := Int.emod_lt_of_pos z (by norm_num)
  have e : ((burnsideF48d_intC z : ℕ) : ℤ) = z % (3 : ℤ) := by
    unfold burnsideF48d_intC
    exact Int.toNat_of_nonneg hr
  have hn : burnsideF48d_intC z < 3 := by omega
  rw [show burnsideF48d_intC z = burnsideF48d_intC z + 3 * 0 + 9 * 0 by ring,
    burnsideF48d_φ_digits ω hn (by norm_num) (by norm_num)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have e2 : (z : K) = ((z % (3 : ℤ) : ℤ) : K) + ((z / (3 : ℤ) : ℤ) : K) * ((3 : ℤ) : K) := by
    rw [← Int.cast_mul, ← Int.cast_add, Int.emod_add_ediv_mul]
  rw [e2, h3, mul_zero, add_zero, ← e, Int.cast_natCast]

end Codes

@[expose] def burnsideF48d_subC (a b : ℕ) : ℕ :=
  (a % 3 + 2 * (b % 3)) % 3 + 3 * ((a / 3 % 3 + 2 * (b / 3 % 3)) % 3) +
    9 * ((a / 9 % 3 + 2 * (b / 9 % 3)) % 3)

section Inj

variable {K : Type*} [Field K] [CharP K 3] (ω : K)

theorem burnsideF48d_φ_sub (a b : ℕ) :
    burnsideF48d_φ ω (burnsideF48d_subC a b) = burnsideF48d_φ ω a - burnsideF48d_φ ω b := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  unfold burnsideF48d_subC
  rw [burnsideF48d_φ_digits ω (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))]
  simp only [burnsideF48d_φ]
  generalize a % 3 = a0
  generalize a / 3 % 3 = a1
  generalize a / 9 % 3 = a2
  generalize b % 3 = b0
  generalize b / 3 % 3 = b1
  generalize b / 9 % 3 = b2
  simp only [burnsideF48d_cast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linear_combination ((b0 : K) + (b1 : K) * ω + (b2 : K) * ω ^ 2) * h3

theorem burnsideF48d_exists_inv : ∀ a < 27, a ≠ 0 → ∃ b < 27, burnsideF48d_mulC a b = 1 := by
  decide

theorem burnsideF48d_eq_of_subC : ∀ a < 27, ∀ b < 27, burnsideF48d_subC a b = 0 → a = b := by
  decide

theorem burnsideF48d_subC_lt (a b : ℕ) : burnsideF48d_subC a b < 27 := by
  unfold burnsideF48d_subC
  omega

theorem burnsideF48d_φ_injOn (hω : ω ^ 3 = ω + 1) {a b : ℕ} (ha : a < 27) (hb : b < 27)
    (h : burnsideF48d_φ ω a = burnsideF48d_φ ω b) : a = b := by
  have hs : burnsideF48d_φ ω (burnsideF48d_subC a b) = 0 := by
    rw [burnsideF48d_φ_sub, h, sub_self]
  by_contra hne
  have hne' : burnsideF48d_subC a b ≠ 0 := fun h0 => hne (burnsideF48d_eq_of_subC a ha b hb h0)
  obtain ⟨c, -, hc⟩ := burnsideF48d_exists_inv _ (burnsideF48d_subC_lt a b) hne'
  have := burnsideF48d_φ_mul ω hω (burnsideF48d_subC a b) c
  rw [hc, hs, zero_mul, burnsideF48d_φ_one] at this
  exact one_ne_zero this

end Inj

theorem burnsideF48d_exists_omega {K : Type*} [Field K] [Fintype K] (hK : Fintype.card K = 27) :
    ∃ ω : K, ω ^ 3 = ω + 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 3 := charP_of_card_eq_prime_pow (f := 3) (by rw [hK]; norm_num)
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hcard : Fintype.card Kˣ = 26 := by
    rw [Fintype.card_units, hK]
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 13 (by rw [hcard]; norm_num)
  set g : K := (u : K) with hg
  have h13 : g ^ 13 = 1 := by
    rw [hg, ← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hg1 : g + 2 ≠ 0 := by
    intro h
    have : g = 1 := by linear_combination h - h3
    have hu1 : u = 1 := Units.ext this
    rw [hu1, orderOf_one] at hu
    norm_num at hu
  have hprod : (g ^ 3 + 2 * g + 2) * (g ^ 3 + g ^ 2 + 2) * (g ^ 3 + g ^ 2 + g + 2) *
      (g ^ 3 + 2 * g ^ 2 + 2 * g + 2) = 0 := by
    have h : (g + 2) * ((g ^ 3 + 2 * g + 2) * (g ^ 3 + g ^ 2 + 2) * (g ^ 3 + g ^ 2 + g + 2) *
        (g ^ 3 + 2 * g ^ 2 + 2 * g + 2)) = 0 := by
      linear_combination h13 - (-2 * g ^ 12 - 6 * g ^ 11 - 15 * g ^ 10 - 32 * g ^ 9 - 54 * g ^ 8 -
        80 * g ^ 7 - 104 * g ^ 6 - 112 * g ^ 5 - 108 * g ^ 4 - 88 * g ^ 3 - 56 * g ^ 2 - 32 * g -
        11) * h3
    exact (mul_eq_zero.1 h).resolve_left hg1
  rcases mul_eq_zero.1 hprod with h | h4
  · rcases mul_eq_zero.1 h with h | h3'
    · rcases mul_eq_zero.1 h with h1 | h2
      · exact ⟨g, by linear_combination h1 + (-g - 1) * h3⟩
      · refine ⟨g ^ 4, ?_⟩
        linear_combination (g ^ 9 - g ^ 8 + g ^ 7 - 3 * g ^ 6 + 5 * g ^ 5 - 7 * g ^ 4 +
          13 * g ^ 3 - 23 * g ^ 2 + 36 * g - 62) * h2 + (36 * g ^ 2 - 24 * g + 41) * h3
    · refine ⟨g ^ 7, ?_⟩
      linear_combination (g ^ 5 - 2 * g ^ 4 + g ^ 3 - g ^ 2 + 4 * g - 5) * h3' + g ^ 8 * h13 +
        (g ^ 2 - g + 3) * h3
  · refine ⟨g ^ 2, ?_⟩
    linear_combination (g ^ 3 - 2 * g ^ 2 + 2 * g - 2) * h4 + (g ^ 2 + 1) * h3

end CFSG.ASVolI
