module

public import CFSG.RankThree.PartOne.SRC.RankOneAux
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.PartOne.SRC

theorem pow_sub_pow_eq_mul (p i d : ℕ) : p ^ (i + d + 1) - p ^ i = p ^ i * (p ^ (d + 1) - 1) := by
  rw [Nat.mul_sub, mul_one, ← pow_add, add_assoc]

theorem sq_sub_one_eq (x : ℕ) : x ^ 2 - 1 = (x + 1) * (x - 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : (y + 1) ^ 2 = y ^ 2 + 2 * y + 1 := by ring
    have h2 : (y + 1 + 1) * y = y ^ 2 + 2 * y := by ring
    omega

theorem not_prime_dvd_card_GL {p r n : ℕ} [Fact p.Prime] (hr : r.Prime) (hrp : ¬ r ∣ p)
    (h1 : ¬ r ∣ p - 1) (h2 : ¬ r ∣ p ^ 2 - 1) (h3 : ¬ r ∣ p ^ 3 - 1) (hn : n ≤ 3) :
    ¬ r ∣ Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) := by
  rw [Matrix.card_GL_field (𝔽 := ZMod p) n, ZMod.card]
  intro hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp hdvd
  obtain ⟨d, hd⟩ : ∃ d, n = (i : ℕ) + d + 1 := ⟨n - (i : ℕ) - 1, by have := i.2; omega⟩
  have hfac : p ^ n - p ^ (i : ℕ) = p ^ (i : ℕ) * (p ^ (d + 1) - 1) := by
    have := pow_sub_pow_eq_mul p (i : ℕ) d
    rwa [← hd] at this
  rw [hfac] at hi
  rcases (Nat.Prime.dvd_mul hr).mp hi with h | h
  · exact hrp (hr.dvd_of_dvd_pow h)
  · have hd2 : d ≤ 2 := by have := i.2; omega
    interval_cases d
    · exact h1 (by simpa using h)
    · exact h2 (by simpa using h)
    · exact h3 h

theorem exists_big_prime_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ p ^ 2 + 1 ∧ ¬ r ∣ p ∧ ¬ r ∣ p - 1 ∧ ¬ r ∣ p ^ 2 - 1 ∧
      ¬ r ∣ p ^ 3 - 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨k, hk⟩ := hodd
  have hm : p ^ 2 + 1 = 2 * (2 * (k * (k + 1)) + 1) := by rw [hk]; ring
  have hk1 : 1 ≤ k := by omega
  have hm1 : 2 * (k * (k + 1)) + 1 ≠ 1 := by
    have : 0 < k * (k + 1) := Nat.mul_pos hk1 (by omega)
    omega
  have hmodd : ¬ 2 ∣ 2 * (k * (k + 1)) + 1 := by omega
  set r := (2 * (k * (k + 1)) + 1).minFac with hrdef
  have hr : r.Prime := Nat.minFac_prime hm1
  have hrm : r ∣ 2 * (k * (k + 1)) + 1 := Nat.minFac_dvd _
  have hr2 : r ≠ 2 := fun h => hmodd (h ▸ hrm)
  have hrd : r ∣ p ^ 2 + 1 := by rw [hm]; exact Dvd.dvd.mul_left hrm 2
  have : Fact r.Prime := ⟨hr⟩
  have hP : (p : ZMod r) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (p ^ 2 + 1) r).mpr hrd
    push_cast at this
    exact this
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 r).mp this))
  have hpos : 1 ≤ p := by omega
  refine ⟨r, hr, hr2, hrd, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 : (p : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff p r).mpr h
    rw [h0] at hP
    simp at hP
  · intro h
    have h0 := (ZMod.natCast_eq_zero_iff (p - 1) r).mpr h
    rw [Nat.cast_sub hpos, Nat.cast_one] at h0
    apply h2
    linear_combination hP - ((p : ZMod r) + 1) * h0
  · intro h
    have h0 := (ZMod.natCast_eq_zero_iff (p ^ 2 - 1) r).mpr h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hpos), Nat.cast_pow, Nat.cast_one] at h0
    apply h2
    linear_combination hP - h0
  · intro h
    have h0 := (ZMod.natCast_eq_zero_iff (p ^ 3 - 1) r).mpr h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hpos), Nat.cast_pow, Nat.cast_one] at h0
    apply h2
    linear_combination (1 - ((p : ZMod r) - 1) * (p : ZMod r)) * hP + ((p : ZMod r) - 1) * h0

theorem not_nine_dvd {p : ℕ} (hp : 1 ≤ p) : ¬ 9 ∣ p * (p - 1) + 1 := by
  intro h
  have h0 := (ZMod.natCast_eq_zero_iff (p * (p - 1) + 1) 9).mpr h
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp, Nat.cast_one] at h0
  have key : ∀ x : ZMod 9, x * (x - 1) + 1 ≠ 0 := by decide
  exact key _ h0

theorem exists_big_prime_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ p ^ 3 + 1 ∧ ¬ r ∣ p ∧ ¬ r ∣ p - 1 ∧ ¬ r ∣ p ^ 2 - 1 ∧
      ¬ r ∣ p ^ 3 - 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpos : 1 ≤ p := by omega
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  set m := p * (p - 1) + 1 with hmdef
  have hmge : 7 ≤ m := by
    rw [hmdef, hq]
    have : 3 ≤ q + 1 := by omega
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hmodd : ¬ 2 ∣ m := by
    have := Nat.even_mul_pred_self p
    rw [hmdef]
    rcases this with ⟨t, ht⟩
    omega
  have hm3 : p ^ 3 + 1 = (p + 1) * m := by
    rw [hmdef, hq]
    simp only [Nat.add_sub_cancel]
    ring
  obtain ⟨r, hr, hrm, hr3⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ m ∧ r ≠ 3 := by
    by_contra hno
    push Not at hno
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) (n := m) (by omega)
      (fun {d} hd hdvd => hno d hd hdvd)
    set L := m.primeFactorsList.length with hL
    have hL2 : 2 ≤ L := by
      by_contra hlt
      push Not at hlt
      interval_cases L <;> simp at hpow <;> omega
    have h9 : 9 ∣ 3 ^ L := by
      have := pow_dvd_pow 3 hL2
      norm_num at this
      exact this
    exact not_nine_dvd hpos (by rw [← hmdef, hpow]; exact h9)
  have hr2 : r ≠ 2 := fun h => hmodd (h ▸ hrm)
  have : Fact r.Prime := ⟨hr⟩
  have hrd : r ∣ p ^ 3 + 1 := by rw [hm3]; exact Dvd.dvd.mul_left hrm _
  have hP : (p : ZMod r) ^ 2 - p + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff m r).mpr hrm
    rw [hmdef, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one] at h0
    linear_combination h0
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 r).mp this))
  have h3 : (3 : ZMod r) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff 3 r).mp this))
  refine ⟨r, hr, hr2, hrd, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 : (p : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff p r).mpr h
    rw [h0] at hP
    simp at hP
  · intro h
    have h0 := (ZMod.natCast_eq_zero_iff (p - 1) r).mpr h
    rw [Nat.cast_sub hpos, Nat.cast_one] at h0
    have hP1 : (p : ZMod r) = 1 := sub_eq_zero.mp h0
    rw [hP1] at hP
    simp at hP
  · intro h
    have h0 := (ZMod.natCast_eq_zero_iff (p ^ 2 - 1) r).mpr h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hpos), Nat.cast_pow, Nat.cast_one] at h0
    apply h3
    linear_combination (1 - ((p : ZMod r) + 2)) * h0 + ((p : ZMod r) + 2) * hP
  · intro h
    have h0 := (ZMod.natCast_eq_zero_iff (p ^ 3 - 1) r).mpr h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hpos), Nat.cast_pow, Nat.cast_one] at h0
    apply h2
    linear_combination ((p : ZMod r) + 1) * hP - h0

@[expose] def BigAt (p : ℕ) (F : Type*) [Field F] [Finite F] : Prop :=
  ∃ m : ℕ, Nat.Coprime m 2 ∧ m ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ∧
    ∀ n : ℕ, n ≤ 3 → ¬ m ∣ Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod p))

theorem bigAt_of_card {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e) {F : Type*} [Field F]
    [Finite F] (hF : Nat.card F = p ^ e) : BigAt p F := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  by_cases he4 : 4 ≤ e
  · refine ⟨p ^ 4, ?_, ?_, fun n hn => not_pow_four_dvd_card_GL hn⟩
    · exact Nat.coprime_two_right.mpr hpodd.pow
    · rw [hSL]
      exact Dvd.dvd.mul_right (pow_dvd_pow p he4) _
  · have he23 : e = 2 ∨ e = 3 := by omega
    rcases he23 with rfl | rfl
    · obtain ⟨r, hr, hr2, hrd, h1, h2, h3, h4⟩ := exists_big_prime_two hp hp2
      refine ⟨r, ?_, ?_, fun n hn => not_prime_dvd_card_GL hr h1 h2 h3 h4 hn⟩
      · exact (Nat.coprime_primes hr Nat.prime_two).mpr hr2
      · rw [hSL]
        refine Dvd.dvd.mul_left ?_ _
        rw [sq_sub_one_eq (p ^ 2)]
        exact Dvd.dvd.mul_right hrd _
    · obtain ⟨r, hr, hr2, hrd, h1, h2, h3, h4⟩ := exists_big_prime_three hp hp2
      refine ⟨r, ?_, ?_, fun n hn => not_prime_dvd_card_GL hr h1 h2 h3 h4 hn⟩
      · exact (Nat.coprime_primes hr Nat.prime_two).mpr hr2
      · rw [hSL]
        refine Dvd.dvd.mul_left ?_ _
        rw [sq_sub_one_eq (p ^ 3)]
        exact Dvd.dvd.mul_right hrd _

end CFSG.RankThree.PartOne.SRC
