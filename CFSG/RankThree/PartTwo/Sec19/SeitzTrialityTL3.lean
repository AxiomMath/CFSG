module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec19.TrialityArith

theorem dvd_comb_aux {p x y : ℤ} (hx : p ∣ x) (hy : p ∣ y) (a b c : ℤ)
    (h : c = a * x + b * y) : p ∣ c := by
  rw [h]
  exact dvd_add (Dvd.dvd.mul_left hx a) (Dvd.dvd.mul_left hy b)

theorem not_dvd_small_aux {p : ℕ} (hp5 : 5 ≤ p) {c : ℤ} (hc0 : 0 < c) (hc3 : c ≤ 3)
    (h : (p : ℤ) ∣ c) : False := by
  have hle := Int.le_of_dvd hc0 h
  omega

theorem torusN_form {q N : ℕ} {ε : ℤ} (hq4 : 4 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (hcong : (q : ℤ) ≡ ε [ZMOD 3]) (hN : (N : ℤ) = (q : ℤ) ^ 2 + ε * (q : ℤ) + 1) :
    ∃ m : ℤ, (N : ℤ) = 9 * m + 3 ∧ 2 ≤ m := by
  have hq4' : (4 : ℤ) ≤ q := by exact_mod_cast hq4
  unfold Int.ModEq at hcong
  rcases hε with rfl | rfl
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, (q : ℤ) = 3 * k + 1 := ⟨(q : ℤ) / 3, by omega⟩
    refine ⟨k ^ 2 + k, ?_, ?_⟩
    · rw [hN, hk]; ring
    · have hk1 : 1 ≤ k := by omega
      nlinarith
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, (q : ℤ) = 3 * k - 1 := ⟨((q : ℤ) + 1) / 3, by omega⟩
    refine ⟨k ^ 2 - k, ?_, ?_⟩
    · rw [hN, hk]; ring
    · have hk2 : 2 ≤ k := by omega
      nlinarith

theorem three_dvd_torusN {q N : ℕ} {ε : ℤ} (hq4 : 4 ≤ q) (hq2 : 2 ∣ q)
    (hε : ε = 1 ∨ ε = -1) (hcong : (q : ℤ) ≡ ε [ZMOD 3])
    (hN : (N : ℤ) = (q : ℤ) ^ 2 + ε * (q : ℤ) + 1) :
    3 ∣ N ∧ ¬ 9 ∣ N ∧ Odd N ∧ 7 ≤ N / 3 := by
  obtain ⟨m, hm, hm2⟩ := torusN_form hq4 hε hcong hN
  obtain ⟨r, hr⟩ := hq2
  have hr' : (q : ℤ) = 2 * (r : ℤ) := by exact_mod_cast hr
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (N : ℤ) = 2 * s + 1 := by
    rcases hε with rfl | rfl
    · exact ⟨2 * (r : ℤ) ^ 2 + (r : ℤ), by rw [hN, hr']; ring⟩
    · exact ⟨2 * (r : ℤ) ^ 2 - (r : ℤ), by rw [hN, hr']; ring⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact Nat.odd_iff.mpr (by omega)
  · omega

theorem exists_prime_dvd_torusN {q N : ℕ} {ε : ℤ} (hq4 : 4 ≤ q) (hq2 : 2 ∣ q)
    (hε : ε = 1 ∨ ε = -1) (hcong : (q : ℤ) ≡ ε [ZMOD 3])
    (hN : (N : ℤ) = (q : ℤ) ^ 2 + ε * (q : ℤ) + 1) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ N := by
  obtain ⟨h3, h9, hodd, h7⟩ := three_dvd_torusN hq4 hq2 hε hcong hN
  have hodd' : N % 2 = 1 := Nat.odd_iff.mp hodd
  obtain ⟨M, hM⟩ := h3
  have hM7 : M ≠ 1 := by omega
  have hM3 : ¬ 3 ∣ M := by omega
  have hM2 : ¬ 2 ∣ M := by omega
  obtain ⟨p, hpdef⟩ : ∃ p, p = M.minFac := ⟨_, rfl⟩
  have hp : p.Prime := by rw [hpdef]; exact Nat.minFac_prime hM7
  have hpM : p ∣ M := by rw [hpdef]; exact Nat.minFac_dvd M
  have hpN : p ∣ N := by rw [hM]; exact Dvd.dvd.mul_left hpM 3
  refine ⟨p, hp, ?_, hpN⟩
  have hp2 := hp.two_le
  by_contra hlt
  have hle : p ≤ 4 := by omega
  interval_cases p
  · exact hM2 hpM
  · exact hM3 hpM
  ·
    rcases hp.eq_one_or_self_of_dvd 2 (by norm_num) with h | h <;> omega

theorem plus_not_dvd_q {p : ℕ} (hp5 : 5 ≤ p) {q : ℤ} (hpN : (p : ℤ) ∣ q ^ 2 + q + 1)
    (hq : (p : ℤ) ∣ q) : False :=
  not_dvd_small_aux hp5 (by norm_num : (0 : ℤ) < 1) (by norm_num : (1 : ℤ) ≤ 3)
    (dvd_comb_aux hpN hq 1 (-(q + 1)) 1 (by ring))

theorem plus_not_dvd_A {p : ℕ} (hp5 : 5 ≤ p) {q : ℤ} (hpN : (p : ℤ) ∣ q ^ 2 + q + 1)
    (hA : (p : ℤ) ∣ q ^ 2 - q + 1) : False :=
  not_dvd_small_aux hp5 (by norm_num : (0 : ℤ) < 2) (by norm_num : (2 : ℤ) ≤ 3)
    (dvd_comb_aux hpN hA (1 - q) (q + 1) 2 (by ring))

theorem plus_not_dvd_B {p : ℕ} (hp5 : 5 ≤ p) {q : ℤ} (hpN : (p : ℤ) ∣ q ^ 2 + q + 1)
    (hB : (p : ℤ) ∣ q ^ 4 - q ^ 2 + 1) : False := by
  have h2q : (p : ℤ) ∣ 2 * (q + 1) :=
    dvd_comb_aux hB hpN 1 (-(q ^ 2 - q - 1)) (2 * (q + 1)) (by ring)
  exact not_dvd_small_aux hp5 (by norm_num : (0 : ℤ) < 2) (by norm_num : (2 : ℤ) ≤ 3)
    (dvd_comb_aux hpN h2q 2 (-q) 2 (by ring))

theorem plus_not_dvd_C {p : ℕ} (hp5 : 5 ≤ p) {q : ℤ} (hpN : (p : ℤ) ∣ q ^ 2 + q + 1)
    (hC : (p : ℤ) ∣ q ^ 2 - 1) : False :=
  not_dvd_small_aux hp5 (by norm_num : (0 : ℤ) < 3) (by norm_num : (3 : ℤ) ≤ 3)
    (dvd_comb_aux hpN hC (2 - q) (q - 1) 3 (by ring))

theorem cofactor_plus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {q N : ℤ}
    (hN : N = q ^ 2 + q + 1) (hpN : (p : ℤ) ∣ N) :
    ∃ M : ℤ, q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) = N ^ 2 * M ∧
      ¬ (p : ℤ) ∣ M := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  subst hN
  refine ⟨q ^ 12 * (q ^ 2 - q + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1) * (q ^ 2 - 1) ^ 2, by ring, ?_⟩
  intro hdvd
  rcases hpZ.dvd_or_dvd hdvd with h1 | h1
  · rcases hpZ.dvd_or_dvd h1 with h2 | h2
    · rcases hpZ.dvd_or_dvd h2 with h3 | h3
      · exact plus_not_dvd_q hp5 hpN (hpZ.dvd_of_dvd_pow h3)
      · exact plus_not_dvd_A hp5 hpN (hpZ.dvd_of_dvd_pow h3)
    · exact plus_not_dvd_B hp5 hpN h2
  · exact plus_not_dvd_C hp5 hpN (hpZ.dvd_of_dvd_pow h1)

theorem cofactor_minus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {q N : ℤ}
    (hN : N = q ^ 2 - q + 1) (hpN : (p : ℤ) ∣ N) :
    ∃ M : ℤ, q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) = N ^ 2 * M ∧
      ¬ (p : ℤ) ∣ M := by
  obtain ⟨M, hM, hnd⟩ :=
    cofactor_plus (q := -q) (N := N) hp hp5 (by linear_combination hN) hpN
  exact ⟨M, by linear_combination hM, hnd⟩

theorem cofactor_torus {q N : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hN : (N : ℤ) = (q : ℤ) ^ 2 + ε * (q : ℤ) + 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpN : p ∣ N) :
    ∃ M : ℤ, (q : ℤ) ^ 12 * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) * ((q : ℤ) ^ 6 - 1) *
        ((q : ℤ) ^ 2 - 1) = (N : ℤ) ^ 2 * M ∧ ¬ (p : ℤ) ∣ M := by
  have hpN' : (p : ℤ) ∣ (N : ℤ) := by exact_mod_cast hpN
  rcases hε with rfl | rfl
  · exact cofactor_plus (q := (q : ℤ)) (N := (N : ℤ)) hp hp5
      (by linear_combination hN) hpN'
  · exact cofactor_minus (q := (q : ℤ)) (N := (N : ℤ)) hp hp5
      (by linear_combination hN) hpN'

theorem padicValNat_order_cofactor {q N : ℕ} {ε : ℤ} (hq4 : 4 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (hN : (N : ℤ) = (q : ℤ) ^ 2 + ε * (q : ℤ) + 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpN : p ∣ N) :
    padicValNat p (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) =
      2 * padicValNat p N := by
  haveI := Fact.mk hp
  have hq4' : (4 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq4
  obtain ⟨M, hM, hpM⟩ := cofactor_torus hε hN hp hp5 hpN
  have hNpos : (0 : ℤ) < (N : ℤ) := by
    rcases hε with rfl | rfl
    · nlinarith [sq_nonneg (q : ℤ)]
    · nlinarith [sq_nonneg ((q : ℤ) - 4)]
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hNpos
  have hK0 : M.natAbs ≠ 0 := by
    intro h0
    apply hpM
    rw [Int.natAbs_eq_zero.mp h0]
    exact dvd_zero _
  have hKnd : ¬ p ∣ M.natAbs := fun h => hpM (Int.natCast_dvd.mpr h)
  have h6 : 1 ≤ q ^ 6 := by
    have := pow_pos (show 0 < q by omega) 6
    omega
  have h2 : 1 ≤ q ^ 2 := by
    have := pow_pos (show 0 < q by omega) 2
    omega
  have hPZ : ((q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) : ℕ) : ℤ) =
      (q : ℤ) ^ 12 * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) * ((q : ℤ) ^ 6 - 1) *
        ((q : ℤ) ^ 2 - 1) := by
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] <;> ring
  have hPM : ((q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) : ℕ) : ℤ) =
      (N : ℤ) ^ 2 * M := hPZ.trans hM
  have hPnat : q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) =
      N ^ 2 * M.natAbs := by
    have h := congrArg Int.natAbs hPM
    rw [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h
    exact h
  rw [hPnat, padicValNat.mul (p := p) (pow_ne_zero 2 hN0) hK0,
    padicValNat.pow (p := p) N 2, padicValNat.eq_zero_of_not_dvd (p := p) hKnd, add_zero]

theorem torus_arith (q n N : ℕ) (ε : ℤ) (hn : 2 ≤ n) (hq : q = 2 ^ n)
    (hε : ε = 1 ∨ ε = -1) (hcong : (q : ℤ) ≡ ε [ZMOD 3])
    (hN : (N : ℤ) = (q : ℤ) ^ 2 + ε * (q : ℤ) + 1) :
    (3 ∣ N ∧ ¬ 9 ∣ N ∧ Odd N ∧ 7 ≤ N / 3) ∧
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ N) ∧
      (∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ N →
        padicValNat p (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) =
          2 * padicValNat p N) := by
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq2 : 2 ∣ q := by
    rw [hq]
    exact dvd_pow_self 2 (by omega)
  exact ⟨three_dvd_torusN hq4 hq2 hε hcong hN, exists_prime_dvd_torusN hq4 hq2 hε hcong hN,
    fun p hp hp5 hpN => padicValNat_order_cofactor hq4 hε hN hp hp5 hpN⟩

end CFSG.RankThree.PartTwo.Sec19.TrialityArith
