module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

@[expose] def targetOrder (x m : ℕ) : Prop :=
  m = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) ∨ m = x ^ 4 * ((x ^ 2 - 1) * (x ^ 4 - 1)) ∨
    m = x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1))

private theorem knl_two_le_pow {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 2 ^ n :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

private theorem knl_odd_pow_sub_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Odd ((2 ^ n) ^ k - 1) := by
  have h1 : 2 ∣ (2 ^ n) ^ k := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
  have h2 : 1 ≤ (2 ^ n) ^ k := Nat.one_le_pow _ _ (by positivity)
  rw [Nat.odd_iff]
  omega

private theorem knl_odd_pow_add_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Odd ((2 ^ n) ^ k + 1) := by
  have h1 : 2 ∣ (2 ^ n) ^ k := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
  rw [Nat.odd_iff]
  omega

theorem knl_two_pow_mul_odd_inj {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have key : ∀ {a b u v : ℕ}, Odd u → Odd v → a ≤ b → 2 ^ a * u = 2 ^ b * v →
      a = b ∧ u = v := by
    intro a b u v hu hv hab h
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' : u = 2 ^ c * v := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simpa using h'
    · exfalso
      have h2 : 2 ∣ u := h' ▸ Dvd.dvd.mul_right (dvd_pow_self 2 hc.ne') v
      have h3 := Nat.odd_iff.mp hu
      omega
  rcases le_total a b with hab | hba
  · exact key hu hv hab h
  · obtain ⟨h1, h2⟩ := key hv hu hba h.symm
    exact ⟨h1.symm, h2.symm⟩

private theorem knl_sq_sub_one (y : ℕ) : y ^ 2 - 1 = (y + 1) * (y - 1) := by
  have := Nat.sq_sub_sq y 1
  simpa using this

private theorem knl_core_sl3 {x : ℕ} (hx : 2 ≤ x) :
    (x ^ 3) ^ 2 - 1 ≠ (x ^ 2 - 1) * (x ^ 3 - 1) := by
  intro h
  have h3 : 8 ≤ x ^ 3 :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have h23 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [knl_sq_sub_one] at h
  have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < x ^ 3 - 1) h
  omega

private theorem knl_core_sp4 {x : ℕ} (hx : 2 ≤ x) :
    (x ^ 4) ^ 2 - 1 ≠ (x ^ 2 - 1) * (x ^ 4 - 1) := by
  intro h
  have h3 : 16 ≤ x ^ 4 :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ x ^ 4 := Nat.pow_le_pow_left hx 4
  have h23 : x ^ 2 ≤ x ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [knl_sq_sub_one] at h
  have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < x ^ 4 - 1) h
  omega

private theorem knl_core_u4 {x : ℕ} (hx : 2 ≤ x) :
    (x ^ 6) ^ 2 - 1 ≠ (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) := by
  intro h
  have h3 : 8 ≤ x ^ 3 :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have h23 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h46 : x ^ 4 ≤ x ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h6 : x ^ 6 = (x ^ 3) ^ 2 := by rw [← pow_mul]
  have e1 : (x ^ 6) ^ 2 - 1 = (x ^ 6 + 1) * ((x ^ 3 + 1) * (x ^ 3 - 1)) := by
    rw [knl_sq_sub_one (x ^ 6), h6, knl_sq_sub_one (x ^ 3), ← h6]
  have e2 : (x ^ 3 + 1) * ((x ^ 6 + 1) * (x ^ 3 - 1)) =
      (x ^ 3 + 1) * ((x ^ 2 - 1) * (x ^ 4 - 1)) :=
    calc (x ^ 3 + 1) * ((x ^ 6 + 1) * (x ^ 3 - 1))
        = (x ^ 6 + 1) * ((x ^ 3 + 1) * (x ^ 3 - 1)) := by ring
      _ = (x ^ 6) ^ 2 - 1 := e1.symm
      _ = (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) := h
      _ = (x ^ 3 + 1) * ((x ^ 2 - 1) * (x ^ 4 - 1)) := by ring
  have e3 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < x ^ 3 + 1) e2
  have a1 : (x ^ 2 - 1) * (x ^ 4 - 1) ≤ (x ^ 3 - 1) * (x ^ 4 - 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_right h23 1)
  have a2 : (x ^ 3 - 1) * (x ^ 4 - 1) < (x ^ 3 - 1) * (x ^ 6 + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  rw [mul_comm (x ^ 6 + 1)] at e3
  omega

theorem knl_ne_l2_order {n a m : ℕ} (hn : 1 ≤ n) (ha : 1 ≤ a) (hm : targetOrder (2 ^ n) m) :
    m ≠ 2 ^ a * ((2 ^ a) ^ 2 - 1) := by
  intro h
  have hx : 2 ≤ 2 ^ n := knl_two_le_pow hn
  have hodd_a : Odd ((2 ^ a) ^ 2 - 1) := knl_odd_pow_sub_one ha (by norm_num)
  have o2 : Odd ((2 ^ n) ^ 2 - 1) := knl_odd_pow_sub_one hn (by norm_num)
  have o3 : Odd ((2 ^ n) ^ 3 - 1) := knl_odd_pow_sub_one hn (by norm_num)
  have o3' : Odd ((2 ^ n) ^ 3 + 1) := knl_odd_pow_add_one hn (by norm_num)
  have o4 : Odd ((2 ^ n) ^ 4 - 1) := knl_odd_pow_sub_one hn (by norm_num)
  rcases hm with h1 | h1 | h1
  · have h2 : 2 ^ a * ((2 ^ a) ^ 2 - 1) =
        2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [← h, h1, pow_mul]
    obtain ⟨ha3, hodd⟩ := knl_two_pow_mul_odd_inj hodd_a (o2.mul o3) h2
    subst ha3
    rw [pow_mul] at hodd
    exact knl_core_sl3 hx hodd
  · have h2 : 2 ^ a * ((2 ^ a) ^ 2 - 1) =
        2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [← h, h1, pow_mul]
    obtain ⟨ha4, hodd⟩ := knl_two_pow_mul_odd_inj hodd_a (o2.mul o4) h2
    subst ha4
    rw [pow_mul] at hodd
    exact knl_core_sp4 hx hodd
  · have h2 : 2 ^ a * ((2 ^ a) ^ 2 - 1) =
        2 ^ (n * 6) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [← h, h1, pow_mul]
    obtain ⟨ha6, hodd⟩ := knl_two_pow_mul_odd_inj hodd_a ((o2.mul o3').mul o4) h2
    subst ha6
    rw [pow_mul] at hodd
    exact knl_core_u4 hx hodd

private theorem knl_prime_aux {p e M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (h : p * (p ^ 2 - 1) = 2 ^ (e + 1) * M) : p ∣ M ∧ 2 ^ e ≤ p + 1 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hcop : Nat.Coprime p (2 ^ (e + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  refine ⟨?_, ?_⟩
  · have h1 : p ∣ 2 ^ (e + 1) * M := h ▸ dvd_mul_right p _
    exact hcop.dvd_of_dvd_mul_left h1
  · have h2 : 2 ^ (e + 1) ∣ p * (p ^ 2 - 1) := ⟨M, h⟩
    have h3 : 2 ^ (e + 1) ∣ p ^ 2 - 1 := hcop.symm.dvd_of_dvd_mul_left h2
    obtain ⟨u, hu⟩ := hpodd
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    have h4 : p ^ 2 - 1 = 4 * (u * (u + 1)) := by
      have : p ^ 2 = 4 * (u * (u + 1)) + 1 := by rw [hu]; ring
      omega
    have h5 : 2 ^ (f + 1 + 1) = 4 * 2 ^ f := by ring
    rw [h4, h5] at h3
    have h6 : 2 ^ f ∣ u * (u + 1) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
    have key : 2 ^ f ∣ u ∨ 2 ^ f ∣ u + 1 := by
      by_cases hu2 : 2 ∣ u
      · left
        have hc : Nat.Coprime (2 ^ f) (u + 1) :=
          Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ⟨u / 2, by omega⟩)
        exact hc.dvd_of_dvd_mul_right h6
      · right
        have hc : Nat.Coprime (2 ^ f) u :=
          Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ⟨u / 2, by omega⟩)
        exact hc.dvd_of_dvd_mul_left h6
    have h7 : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    rcases key with hk | hk
    · have := Nat.le_of_dvd (by omega) hk
      omega
    · have := Nat.le_of_dvd (by omega) hk
      omega

private theorem knl_sl3_prime {x p : ℕ} (hx : 8 ≤ x) (hp : p.Prime)
    (hd : p ∣ (x ^ 2 - 1) * (x ^ 3 - 1)) (hle : x ^ 3 ≤ p + 1) : False := by
  have h2 : x ^ 2 < x ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have h1' : x ≤ x ^ 2 := Nat.le_self_pow (by norm_num) x
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
  · have h1 : p ≤ x ^ 2 - 1 := Nat.le_of_dvd (by omega) hd
    omega
  · have h1 : p ≤ x ^ 3 - 1 := Nat.le_of_dvd (by omega) hd
    have hpe : p = x ^ 3 - 1 := by omega
    have hdvd : x - 1 ∣ p := hpe ▸ Nat.sub_one_dvd_pow_sub_one x 3
    rcases (Nat.dvd_prime hp).mp hdvd with h5 | h5
    · omega
    · omega

private theorem knl_sp4_prime {x p : ℕ} (hx : 8 ≤ x) (hp : p.Prime)
    (hd : p ∣ (x ^ 2 - 1) * (x ^ 4 - 1)) (hle : x ^ 4 ≤ p + 1) : False := by
  have h2 : x ^ 2 < x ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have h3 : 8 ≤ x ^ 2 :=
    calc 8 ≤ x := hx
      _ ≤ x ^ 2 := Nat.le_self_pow (by norm_num) x
  have h4 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by omega)
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
  · have h1 : p ≤ x ^ 2 - 1 := Nat.le_of_dvd (by omega) hd
    omega
  · have h1 : p ≤ x ^ 4 - 1 := Nat.le_of_dvd (by omega) hd
    have hpe : p = x ^ 4 - 1 := by omega
    have hdvd : x ^ 2 - 1 ∣ p := by
      rw [hpe, show x ^ 4 = (x ^ 2) ^ 2 by rw [← pow_mul]]
      exact Nat.sub_one_dvd_pow_sub_one (x ^ 2) 2
    rcases (Nat.dvd_prime hp).mp hdvd with h5 | h5
    · omega
    · omega

private theorem knl_u4_prime {x p : ℕ} (hx : 8 ≤ x) (hp : p.Prime)
    (hd : p ∣ (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) (hle : x ^ 6 ≤ p + 1) : False := by
  have h2 : x ^ 2 ≤ x ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : x ^ 3 + 1 < x ^ 4 := by
    have h : x ^ 4 = x ^ 3 * x := by ring
    have h' : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h4 : x ^ 4 < x ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have h5 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 8 ≤ x ^ 2 :=
    calc 8 ≤ x := hx
      _ ≤ x ^ 2 := Nat.le_self_pow (by norm_num) x
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · have := Nat.le_of_dvd (by omega) hd
      omega
    · have := Nat.le_of_dvd (by omega) hd
      omega
  · have := Nat.le_of_dvd (by omega) hd
    omega

theorem knl_ne_l2odd_order {n p m : ℕ} (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : targetOrder (2 ^ n) m) : m * 2 ≠ p * (p ^ 2 - 1) := by
  intro h
  have hx : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases hm with h1 | h1 | h1
  · have e : 2 ^ (n * 3 + 1) = (2 ^ n) ^ 3 * 2 := by rw [pow_succ, pow_mul]
    have h2 : p * (p ^ 2 - 1) =
        2 ^ (n * 3 + 1) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [← h, h1, e]; ring
    obtain ⟨hpM, hle⟩ := knl_prime_aux hp hp2 (by omega) h2
    rw [pow_mul] at hle
    exact knl_sl3_prime hx hp hpM hle
  · have e : 2 ^ (n * 4 + 1) = (2 ^ n) ^ 4 * 2 := by rw [pow_succ, pow_mul]
    have h2 : p * (p ^ 2 - 1) =
        2 ^ (n * 4 + 1) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [← h, h1, e]; ring
    obtain ⟨hpM, hle⟩ := knl_prime_aux hp hp2 (by omega) h2
    rw [pow_mul] at hle
    exact knl_sp4_prime hx hp hpM hle
  · have e : 2 ^ (n * 6 + 1) = (2 ^ n) ^ 6 * 2 := by rw [pow_succ, pow_mul]
    have h2 : p * (p ^ 2 - 1) =
        2 ^ (n * 6 + 1) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [← h, h1, e]; ring
    obtain ⟨hpM, hle⟩ := knl_prime_aux hp hp2 (by omega) h2
    rw [pow_mul] at hle
    exact knl_u4_prime hx hp hpM hle

theorem knl_not_dvd_j1 {n m : ℕ} (hn : 3 ≤ n) (hm : targetOrder (2 ^ n) m) :
    ¬ m ∣ 175560 := by
  intro hd
  have h3 : 2 ^ 9 ∣ (2 ^ n) ^ 3 := by
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  have h4 : (2 ^ n) ^ 3 ∣ (2 ^ n) ^ 4 := pow_dvd_pow _ (by norm_num)
  have h6 : (2 ^ n) ^ 3 ∣ (2 ^ n) ^ 6 := pow_dvd_pow _ (by norm_num)
  have h512 : 2 ^ 9 ∣ m := by
    rcases hm with h1 | h1 | h1
    · rw [h1]; exact Dvd.dvd.mul_right h3 _
    · rw [h1]; exact Dvd.dvd.mul_right (h3.trans h4) _
    · rw [h1]; exact Dvd.dvd.mul_right (h3.trans h6) _
  have := h512.trans hd
  revert this
  decide

theorem knl_three_dvd_order {n m : ℕ} (hm : targetOrder (2 ^ n) m) : 3 ∣ m := by
  have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
    have h := Nat.sub_one_dvd_pow_sub_one 4 n
    have e : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]
    simpa using h
  rcases hm with h1 | h1 | h1
  · rw [h1]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _
  · rw [h1]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _
  · rw [h1]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right h3 _) _) _

theorem knl_one_lt_order {n m : ℕ} (hn : 1 ≤ n) (hm : targetOrder (2 ^ n) m) : 1 < m := by
  have hx : 2 ≤ 2 ^ n := knl_two_le_pow hn
  have hx2 : 4 ≤ (2 ^ n) ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hx 2
  have hx3 : 8 ≤ (2 ^ n) ^ 3 :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hx 3
  have hx4 : 16 ≤ (2 ^ n) ^ 4 :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left hx 4
  have hx6 : 64 ≤ (2 ^ n) ^ 6 :=
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left hx 6
  rcases hm with h1 | h1 | h1
  · rw [h1]
    have : 0 < (2 ^ n) ^ 2 - 1 := by omega
    have : 0 < (2 ^ n) ^ 3 - 1 := by omega
    have : 0 < ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · rw [h1]
    have : 0 < ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1) := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · rw [h1]
    have : 0 < ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    nlinarith

theorem knl_ne_square_order {n m : ℕ} (hn : 1 ≤ n) (hm : targetOrder (2 ^ n) m) :
    m ≠ (2 ^ n * ((2 ^ n) ^ 2 - 1)) * (2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
  intro h
  have o2 : Odd ((2 ^ n) ^ 2 - 1) := knl_odd_pow_sub_one hn (by norm_num)
  have o3 : Odd ((2 ^ n) ^ 3 - 1) := knl_odd_pow_sub_one hn (by norm_num)
  have o3' : Odd ((2 ^ n) ^ 3 + 1) := knl_odd_pow_add_one hn (by norm_num)
  have o4 : Odd ((2 ^ n) ^ 4 - 1) := knl_odd_pow_sub_one hn (by norm_num)
  have h0 : (2 ^ n * ((2 ^ n) ^ 2 - 1)) * (2 ^ n * ((2 ^ n) ^ 2 - 1)) =
      2 ^ (n * 2) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - 1)) := by
    generalize (2 ^ n) ^ 2 - 1 = A
    rw [pow_mul]; ring
  rcases hm with h1 | h1 | h1
  · have h2 : 2 ^ (n * 2) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - 1)) =
        2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [← h0, ← h, h1, pow_mul]
    have := (knl_two_pow_mul_odd_inj (o2.mul o2) (o2.mul o3) h2).1
    omega
  · have h2 : 2 ^ (n * 2) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - 1)) =
        2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [← h0, ← h, h1, pow_mul]
    have := (knl_two_pow_mul_odd_inj (o2.mul o2) (o2.mul o4) h2).1
    omega
  · have h2 : 2 ^ (n * 2) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - 1)) =
        2 ^ (n * 6) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [← h0, ← h, h1, pow_mul]
    have := (knl_two_pow_mul_odd_inj (o2.mul o2) ((o2.mul o3').mul o4) h2).1
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

end
