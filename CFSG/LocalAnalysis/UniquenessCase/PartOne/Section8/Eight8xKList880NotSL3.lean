module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves
import CFSG.Adapters.LieModelL3U3Sylow
import CFSG.Adapters.LieModelOrders
import CFSG.GH74.Orders.Sporadic
import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicTable
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31B
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKSU5Center
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.RankThree.PartTwo.Sec21.Hering214KGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

section

private def l3Num (r : ℕ) (minus : Bool) : ℕ :=
  r ^ 3 * ((r ^ 2 - 1) * (if minus then r ^ 3 + 1 else r ^ 3 - 1))

private theorem l3Num_ge (r : ℕ) (b : Bool) : r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) ≤ l3Num r b := by
  unfold l3Num
  cases b
  · simp
  · simp only [if_true]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

private theorem seventeen_mul_lt {r : ℕ} (hr : 4 ≤ r) :
    17 * (r + 1) ^ 5 < r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
  have h2 : (s + 4) ^ 2 - 1 = s ^ 2 + 8 * s + 15 := by
    apply Nat.sub_eq_of_eq_add; ring
  have h3 : (s + 4) ^ 3 - 1 = s ^ 3 + 12 * s ^ 2 + 48 * s + 63 := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [h2, h3]
  have e : (s + 4) ^ 3 * ((s ^ 2 + 8 * s + 15) * (s ^ 3 + 12 * s ^ 2 + 48 * s + 63)) =
      17 * (s + 4 + 1) ^ 5 + (7355 + 70571 * s + 88970 * s ^ 2 + 51655 * s ^ 3 + 17235 * s ^ 4 +
        3542 * s ^ 5 + 447 * s ^ 6 + 32 * s ^ 7 + s ^ 8) := by ring
  rw [e]
  omega

private theorem l3Num_sq_gt {r : ℕ} (b : Bool) (hr : 4 ≤ r) : 288 * (r + 1) ^ 10 < l3Num r b ^ 2 := by
  have h := (seventeen_mul_lt hr).trans_le (l3Num_ge r b)
  have hpos : 0 < (r + 1) ^ 10 := by positivity
  calc 288 * (r + 1) ^ 10 < 289 * (r + 1) ^ 10 := by omega
    _ = (17 * (r + 1) ^ 5) ^ 2 := by ring
    _ < l3Num r b ^ 2 := Nat.pow_lt_pow_left h (by norm_num)

private theorem coprime_two_pow_of_odd (k : ℕ) {m : ℕ} (hm : Odd m) : Nat.Coprime (2 ^ k) m :=
  Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr (by
    rintro ⟨c, hc⟩; obtain ⟨d, hd⟩ := hm; omega))

private theorem two_pow_le_of_dvd_l3Num {r k : ℕ} (b : Bool) (hr : Odd r) (hr1 : 1 < r)
    (h : 2 ^ k ∣ l3Num r b) : 2 ^ k ≤ 2 * (r + 1) ^ 2 := by
  obtain ⟨t, rfl⟩ := hr
  have ht : 1 ≤ t := by omega
  have h2 : (2 * t + 1) ^ 2 - 1 = 4 * t * (t + 1) := by apply Nat.sub_eq_of_eq_add; ring
  have hodd3 : Odd ((2 * t + 1) ^ 3) := Odd.pow ⟨t, rfl⟩
  have key : 2 ^ k ∣ 8 * t ^ 2 * (t + 1) ∨ 2 ^ k ∣ 8 * t * (t + 1) ^ 2 := by
    unfold l3Num at h
    cases b
    · left
      have h3 : (2 * t + 1) ^ 3 - 1 = 2 * t * (4 * t ^ 2 + 6 * t + 3) := by
        apply Nat.sub_eq_of_eq_add; ring
      simp only [Bool.false_eq_true, if_false, h2, h3] at h
      have e : (2 * t + 1) ^ 3 * (4 * t * (t + 1) * (2 * t * (4 * t ^ 2 + 6 * t + 3))) =
          8 * t ^ 2 * (t + 1) * ((2 * t + 1) ^ 3 * (4 * t ^ 2 + 6 * t + 3)) := by ring
      rw [e] at h
      exact (coprime_two_pow_of_odd k (hodd3.mul ⟨2 * t ^ 2 + 3 * t + 1, by ring⟩)).dvd_of_dvd_mul_right h
    · right
      have h3 : (2 * t + 1) ^ 3 + 1 = 2 * (t + 1) * (4 * t ^ 2 + 2 * t + 1) := by ring
      simp only [if_true, h2, h3] at h
      have e : (2 * t + 1) ^ 3 * (4 * t * (t + 1) * (2 * (t + 1) * (4 * t ^ 2 + 2 * t + 1))) =
          8 * t * (t + 1) ^ 2 * ((2 * t + 1) ^ 3 * (4 * t ^ 2 + 2 * t + 1)) := by ring
      rw [e] at h
      exact (coprime_two_pow_of_odd k (hodd3.mul ⟨2 * t ^ 2 + t, by ring⟩)).dvd_of_dvd_mul_right h
  have hgoal : 2 * (2 * t + 1 + 1) ^ 2 = 8 * (t + 1) ^ 2 := by ring
  rw [hgoal]
  rcases Nat.even_or_odd t with ⟨u, hu⟩ | hto
  ·
    have hto1 : Odd (t + 1) := ⟨u, by omega⟩
    have hc := coprime_two_pow_of_odd k hto1
    have hc2 := coprime_two_pow_of_odd k (hto1.pow (n := 2))
    have hd : 2 ^ k ∣ 8 * t ^ 2 := by
      rcases key with hk | hk
      · exact hc.dvd_of_dvd_mul_right hk
      · have e : 8 * t * (t + 1) ^ 2 = 8 * t * (t + 1) ^ 2 := rfl
        exact (hc2.dvd_of_dvd_mul_right hk).trans ⟨t, by ring⟩
    have := Nat.le_of_dvd (by positivity) hd
    nlinarith
  ·
    have hc := coprime_two_pow_of_odd k hto
    have hc2 := coprime_two_pow_of_odd k (hto.pow (n := 2))
    have hd : 2 ^ k ∣ 8 * (t + 1) ^ 2 := by
      rcases key with hk | hk
      · have e : 8 * t ^ 2 * (t + 1) = 8 * (t + 1) * t ^ 2 := by ring
        rw [e] at hk
        exact (hc2.dvd_of_dvd_mul_right hk).trans ⟨t + 1, by ring⟩
      · have e : 8 * t * (t + 1) ^ 2 = 8 * (t + 1) ^ 2 * t := by ring
        rw [e] at hk
        exact hc.dvd_of_dvd_mul_right hk
    exact Nat.le_of_dvd (by positivity) hd

private theorem two_pow_mul_odd_inj {a c A B : ℕ} (hA : Odd A) (hB : Odd B) (h : 2 ^ a * A = 2 ^ c * B) :
    a = c ∧ A = B := by
  have key : ∀ {a c A B : ℕ}, Odd A → 2 ^ a * A = 2 ^ c * B → a < c → False := by
    intro a c A B hA h hac
    have e : 2 ^ c = 2 ^ a * 2 ^ (c - a) := by rw [← pow_add]; congr 1; omega
    rw [e, mul_assoc] at h
    have hA' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    have hev : Even (2 ^ (c - a) * B) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right B
    exact (Nat.not_even_iff_odd.mpr hA) (hA' ▸ hev)
  rcases lt_trichotomy a c with hac | rfl | hca
  · exact (key hA h hac).elim
  · exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩
  · exact (key hB h.symm hca).elim

private theorem odd_two_pow_pow_sub_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : Odd ((2 ^ n) ^ k - 1) := by
  have hev : Even ((2 ^ n) ^ k) := by
    rw [← pow_mul]; exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
  have h1 : 1 ≤ (2 ^ n) ^ k := Nat.one_le_pow _ _ (by positivity)
  exact Nat.Even.sub_odd h1 hev odd_one

private theorem odd_two_pow_pow_add_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : Odd ((2 ^ n) ^ k + 1) := by
  have hev : Even ((2 ^ n) ^ k) := by
    rw [← pow_mul]; exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
  exact hev.add_one

private theorem l3Num_even {p f : ℕ} (b : Bool) (hp : p.Prime) (hr : 4 ≤ p ^ f) (he : Even (p ^ f)) :
    p = 2 ∧ 1 ≤ f ∧ l3Num (p ^ f) b = 2 ^ (3 * f) *
      (((2 ^ f) ^ 2 - 1) * (if b then (2 ^ f) ^ 3 + 1 else (2 ^ f) ^ 3 - 1)) ∧
      Odd (((2 ^ f) ^ 2 - 1) * (if b then (2 ^ f) ^ 3 + 1 else (2 ^ f) ^ 3 - 1)) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hr
  have hp2 : p = 2 := (hp.even_iff).mp (Nat.even_pow.mp he).1
  subst hp2
  refine ⟨rfl, by omega, ?_, ?_⟩
  · unfold l3Num; rw [← pow_mul, mul_comm f 3]
  · refine (odd_two_pow_pow_sub_one (by omega) (by norm_num)).mul ?_
    cases b
    · simpa using odd_two_pow_pow_sub_one (n := f) (by omega) (by norm_num)
    · simpa using odd_two_pow_pow_add_one (n := f) (by omega) (by norm_num)

private theorem odd_case {r a : ℕ} (b : Bool) (hr : Odd r) (hr4 : 4 ≤ r) (hdvd : 2 ^ a ∣ l3Num r b)
    (hlt : l3Num r b ^ 2 < 9 * (2 ^ a) ^ 5) : False := by
  have h1 := two_pow_le_of_dvd_l3Num b hr (by omega) hdvd
  have h2 : (2 ^ a) ^ 5 ≤ (2 * (r + 1) ^ 2) ^ 5 := Nat.pow_le_pow_left h1 5
  have h3 := l3Num_sq_gt b hr4
  have e : 9 * (2 * (r + 1) ^ 2) ^ 5 = 288 * (r + 1) ^ 10 := by ring
  omega

private theorem three_mul_sp4_ne_l3Num {n p f : ℕ} (b : Bool) (hn : 1 ≤ n) (hp : p.Prime)
    (hr : 4 ≤ p ^ f) :
    3 * ((2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1))) ≠ l3Num (p ^ f) b := by
  intro h
  set q := 2 ^ n with hq
  have hq2 : 2 ≤ q := by
    rw [hq]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hA : Odd (3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1))) :=
    (by decide : Odd 3).mul ((odd_two_pow_pow_sub_one hn (by norm_num)).mul
      (odd_two_pow_pow_sub_one hn (by norm_num)))
  have hL : 3 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) =
      2 ^ (4 * n) * (3 * ((q ^ 2 - 1) * (q ^ 4 - 1))) := by
    rw [hq, ← pow_mul, mul_comm n 4]; ring
  rcases Nat.even_or_odd (p ^ f) with he | ho
  · obtain ⟨rfl, hf, hR, hB⟩ := l3Num_even b hp hr he
    rw [hL, hR] at h
    obtain ⟨hnf, hodd⟩ := two_pow_mul_odd_inj hA hB h
    obtain ⟨j, rfl, rfl⟩ : ∃ j, n = 3 * j ∧ f = 4 * j := ⟨n / 3, by omega, by omega⟩
    set Q := 2 ^ j with hQ
    have hQ2 : 2 ≤ Q := by
      rw [hQ]; calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have eq : 2 ^ (3 * j) = Q ^ 3 := by rw [hQ, ← pow_mul, mul_comm]
    have er : 2 ^ (4 * j) = Q ^ 4 := by rw [hQ, ← pow_mul, mul_comm]
    rw [eq, er] at hodd
    simp only [← pow_mul] at hodd
    norm_num at hodd
    have h6 : 4 * Q ^ 6 ≤ Q ^ 8 := by
      have : Q ^ 8 = Q ^ 2 * Q ^ 6 := by ring
      rw [this]; exact Nat.mul_le_mul_right _ (by nlinarith)
    have h6' : 64 ≤ Q ^ 6 := by
      have := Nat.pow_le_pow_left hQ2 6; norm_num at this; exact this
    have h12 : 1 ≤ Q ^ 12 - 1 := by
      have := Nat.pow_le_pow_left hQ2 12; norm_num at this; omega
    have h1 : 3 * (Q ^ 6 - 1) < Q ^ 8 - 1 := by omega
    have h2 : 3 * (Q ^ 6 - 1) * (Q ^ 12 - 1) < (Q ^ 8 - 1) * (Q ^ 12 - 1) :=
      Nat.mul_lt_mul_of_pos_right h1 (by omega)
    cases b
    · simp only [Bool.false_eq_true, if_false] at hodd; rw [← mul_assoc] at hodd; omega
    · simp only [if_true] at hodd
      have h3 : (Q ^ 8 - 1) * (Q ^ 12 - 1) ≤ (Q ^ 8 - 1) * (Q ^ 12 + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [← mul_assoc] at hodd; omega
  · refine odd_case b ho hr ?_ ?_ (a := 4 * n)
    · rw [← h, hL]; exact Dvd.intro _ rfl
    · rw [← h]
      have hlt : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) < q ^ 10 := by
        have a1 : q ^ 2 - 1 < q ^ 2 := by have := Nat.one_le_pow 2 q (by omega); omega
        have a2 : q ^ 4 - 1 < q ^ 4 := by have := Nat.one_le_pow 4 q (by omega); omega
        calc q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) < q ^ 4 * (q ^ 2 * q ^ 4) :=
              Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' a1 a2) (by positivity)
          _ = q ^ 10 := by ring
      have e : (2 ^ (4 * n)) ^ 5 = (q ^ 10) ^ 2 := by rw [hq, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
      rw [e]
      calc (3 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)))) ^ 2
          = 9 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) ^ 2 := by ring
        _ < 9 * (q ^ 10) ^ 2 := by
          have := Nat.pow_lt_pow_left hlt (by norm_num : (2 : ℕ) ≠ 0); omega

private theorem two_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 2 ^ n :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

private theorem three_mul_g2_ne_l3Num {n p f : ℕ} (b : Bool) (hn : 1 ≤ n) (hp : p.Prime)
    (hr : 4 ≤ p ^ f) :
    3 * ((2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))) ≠ l3Num (p ^ f) b := by
  intro h
  set q := 2 ^ n with hq
  have hq2 : 2 ≤ q := two_le_two_pow hn
  have hA : Odd (3 * ((q ^ 6 - 1) * (q ^ 2 - 1))) := by
    rw [hq]; exact (by decide : Odd 3).mul ((odd_two_pow_pow_sub_one hn (by norm_num)).mul
      (odd_two_pow_pow_sub_one hn (by norm_num)))
  have hL : 3 * (q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1))) =
      2 ^ (6 * n) * (3 * ((q ^ 6 - 1) * (q ^ 2 - 1))) := by
    rw [hq, ← pow_mul, mul_comm n 6]; ring
  rcases Nat.even_or_odd (p ^ f) with he | ho
  · obtain ⟨rfl, hf, hR, hB⟩ := l3Num_even b hp hr he
    rw [hL, hR] at h
    obtain ⟨hnf, hodd⟩ := two_pow_mul_odd_inj hA hB h
    obtain rfl : f = 2 * n := by omega
    have er : 2 ^ (2 * n) = q ^ 2 := by rw [hq, ← pow_mul, mul_comm]
    have e4 : (q ^ 2) ^ 2 = q ^ 4 := by ring
    have e6 : (q ^ 2) ^ 3 = q ^ 6 := by ring
    rw [er, e4, e6] at hodd
    have h4 : 4 * q ^ 2 ≤ q ^ 4 := by
      have : q ^ 4 = q ^ 2 * q ^ 2 := by ring
      rw [this]; exact Nat.mul_le_mul_right _ (by nlinarith)
    have h2' : 4 ≤ q ^ 2 := by nlinarith
    have h6 : 1 ≤ q ^ 6 - 1 := by
      have := Nat.pow_le_pow_left hq2 6; norm_num at this; omega
    have h1 : 3 * (q ^ 2 - 1) < q ^ 4 - 1 := by omega
    have h2 : (q ^ 6 - 1) * (3 * (q ^ 2 - 1)) < (q ^ 6 - 1) * (q ^ 4 - 1) :=
      Nat.mul_lt_mul_of_pos_left h1 (by omega)
    have e1 : 3 * ((q ^ 6 - 1) * (q ^ 2 - 1)) = (q ^ 6 - 1) * (3 * (q ^ 2 - 1)) := by ring
    have e2 : (q ^ 6 - 1) * (q ^ 4 - 1) = (q ^ 4 - 1) * (q ^ 6 - 1) := by ring
    rw [e1] at hodd
    cases b
    · simp only [Bool.false_eq_true, if_false] at hodd; omega
    · simp only [if_true] at hodd
      have h3 : (q ^ 4 - 1) * (q ^ 6 - 1) ≤ (q ^ 4 - 1) * (q ^ 6 + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  · refine odd_case b ho hr ?_ ?_ (a := 6 * n)
    · rw [← h, hL]; exact Dvd.intro _ rfl
    · rw [← h]
      have hlt : q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) < q ^ 15 := by
        have a1 : q ^ 6 - 1 < q ^ 6 := by have := Nat.one_le_pow 6 q (by omega); omega
        have a2 : q ^ 2 - 1 < q ^ 2 := by have := Nat.one_le_pow 2 q (by omega); omega
        calc q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) < q ^ 6 * (q ^ 6 * q ^ 2) :=
              Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' a1 a2) (by positivity)
          _ = q ^ 14 := by ring
          _ < q ^ 15 := Nat.pow_lt_pow_right hq2 (by norm_num)
      have e : (2 ^ (6 * n)) ^ 5 = (q ^ 15) ^ 2 := by
        rw [hq, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
      rw [e]
      calc (3 * (q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)))) ^ 2
          = 9 * (q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1))) ^ 2 := by ring
        _ < 9 * (q ^ 15) ^ 2 := by
          have := Nat.pow_lt_pow_left hlt (by norm_num : (2 : ℕ) ≠ 0); omega

private theorem u5_odd_lt {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) < q ^ 14 := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have a1 : (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 5 := by
    zify [h2]
    have : (q : ℤ) ^ 2 < q ^ 3 + 1 := by
      have : (q : ℤ) ^ 3 = q * q ^ 2 := by ring
      nlinarith [show (2 : ℤ) ≤ q by exact_mod_cast hq, pow_pos (show (0 : ℤ) < q by omega) 2]
    nlinarith
  have a2 : (q ^ 4 - 1) * (q ^ 5 + 1) < q ^ 9 := by
    zify [h4]
    have : (q : ℤ) ^ 4 < q ^ 5 + 1 := by
      have : (q : ℤ) ^ 5 = q * q ^ 4 := by ring
      nlinarith [show (2 : ℤ) ≤ q by exact_mod_cast hq, pow_pos (show (0 : ℤ) < q by omega) 4]
    nlinarith
  calc (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)
      = ((q ^ 2 - 1) * (q ^ 3 + 1)) * ((q ^ 4 - 1) * (q ^ 5 + 1)) := by ring
    _ < q ^ 5 * q ^ 9 := Nat.mul_lt_mul'' a1 a2
    _ = q ^ 14 := by ring

private theorem three_mul_u5_ne_l3Num {m p f : ℕ} (b : Bool) (hm : 1 ≤ m) (hp : p.Prime)
    (hr : 4 ≤ p ^ f) :
    3 * ((2 ^ m) ^ 10 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1) *
      ((2 ^ m) ^ 5 + 1))) ≠ Nat.gcd 5 (2 ^ m + 1) * l3Num (p ^ f) b := by
  intro h
  set q := 2 ^ m with hq
  have hq2 : 2 ≤ q := two_le_two_pow hm
  set d := Nat.gcd 5 (q + 1) with hd
  have hd5 : d = 1 ∨ d = 5 := (Nat.dvd_prime (by norm_num)).mp (Nat.gcd_dvd_left 5 _)
  have hdodd : Odd d := by rcases hd5 with h | h <;> rw [h] <;> decide
  set X := (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) with hX
  have hXodd : Odd X :=
    (((odd_two_pow_pow_sub_one hm (by norm_num)).mul (odd_two_pow_pow_add_one hm (by norm_num))).mul
      (odd_two_pow_pow_sub_one hm (by norm_num))).mul (odd_two_pow_pow_add_one hm (by norm_num))
  have hL : 3 * (q ^ 10 * X) = 2 ^ (10 * m) * (3 * X) := by
    rw [hq, ← pow_mul, mul_comm m 10]; ring
  rw [hL] at h
  rcases Nat.even_or_odd (p ^ f) with he | ho
  · obtain ⟨rfl, hf, hR, hB⟩ := l3Num_even b hp hr he
    have h' : 2 ^ (10 * m) * (3 * X) = 2 ^ (3 * f) *
        (d * (((2 ^ f) ^ 2 - 1) * (if b then (2 ^ f) ^ 3 + 1 else (2 ^ f) ^ 3 - 1))) := by
      rw [h, hR]; ring
    obtain ⟨hmf, hodd⟩ := two_pow_mul_odd_inj ((by decide : Odd 3).mul hXodd) (hdodd.mul hB) h'
    obtain ⟨j, rfl, rfl⟩ : ∃ j, m = 3 * j ∧ f = 10 * j := ⟨m / 3, by omega, by omega⟩
    set Q := 2 ^ j with hQ
    have hQ2 : 2 ≤ Q := two_le_two_pow (by omega)
    have eq : q = Q ^ 3 := by rw [hq, hQ, ← pow_mul, mul_comm]
    have er : 2 ^ (10 * j) = Q ^ 10 := by rw [hQ, ← pow_mul, mul_comm]
    have e20 : (Q ^ 10) ^ 2 = Q ^ 20 := by ring
    have e30 : (Q ^ 10) ^ 3 = Q ^ 30 := by ring
    rw [er, e20, e30] at hodd
    have hXlt : X < q ^ 14 := u5_odd_lt hq2
    have hq14 : q ^ 14 = Q ^ 42 := by rw [eq, ← pow_mul]
    have h20 : Q ^ 20 ≤ 2 * (Q ^ 20 - 1) := by
      have := Nat.pow_le_pow_left hQ2 20; norm_num at this; omega
    have h30 : Q ^ 30 ≤ 2 * (Q ^ 30 - 1) := by
      have := Nat.pow_le_pow_left hQ2 30; norm_num at this; omega
    have h8 : 256 ≤ Q ^ 8 := by have := Nat.pow_le_pow_left hQ2 8; norm_num at this; exact this
    have hprod : Q ^ 50 ≤ 4 * ((Q ^ 20 - 1) * (Q ^ 30 - 1)) := by
      calc Q ^ 50 = Q ^ 20 * Q ^ 30 := by ring
        _ ≤ (2 * (Q ^ 20 - 1)) * (2 * (Q ^ 30 - 1)) := Nat.mul_le_mul h20 h30
        _ = 4 * ((Q ^ 20 - 1) * (Q ^ 30 - 1)) := by ring
    have h50 : 256 * Q ^ 42 ≤ Q ^ 50 := by
      have : Q ^ 50 = Q ^ 8 * Q ^ 42 := by ring
      rw [this]; exact Nat.mul_le_mul_right _ h8
    have hlow : (Q ^ 20 - 1) * (Q ^ 30 - 1) ≤ d * ((Q ^ 20 - 1) * (if b then Q ^ 30 + 1 else Q ^ 30 - 1)) := by
      have hd1 : 1 ≤ d := by rcases hd5 with h | h <;> omega
      calc (Q ^ 20 - 1) * (Q ^ 30 - 1) ≤ (Q ^ 20 - 1) * (if b then Q ^ 30 + 1 else Q ^ 30 - 1) := by
            cases b
            · simp
            · simp only [if_true]; exact Nat.mul_le_mul_left _ (by omega)
        _ ≤ d * ((Q ^ 20 - 1) * (if b then Q ^ 30 + 1 else Q ^ 30 - 1)) := Nat.le_mul_of_pos_left _ hd1
    omega
  · have hdvd : 2 ^ (10 * m) ∣ l3Num (p ^ f) b := by
      have h' : 2 ^ (10 * m) ∣ d * l3Num (p ^ f) b := h ▸ Dvd.intro _ rfl
      exact (coprime_two_pow_of_odd _ hdodd).dvd_of_dvd_mul_left h'
    refine odd_case b ho hr hdvd ?_
    have hd1 : 1 ≤ d := by rcases hd5 with h | h <;> omega
    have hle : l3Num (p ^ f) b ≤ 2 ^ (10 * m) * (3 * X) := h ▸ Nat.le_mul_of_pos_left _ hd1
    have hXlt : X < q ^ 14 := u5_odd_lt hq2
    have hlt : 2 ^ (10 * m) * (3 * X) < 3 * q ^ 25 := by
      have e : 2 ^ (10 * m) = q ^ 10 := by rw [hq, ← pow_mul, mul_comm]
      rw [e]
      calc q ^ 10 * (3 * X) < q ^ 10 * (3 * q ^ 14) :=
            Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
        _ = 3 * q ^ 24 := by ring
        _ < 3 * q ^ 25 := by have := Nat.pow_lt_pow_right hq2 (by norm_num : 24 < 25); omega
    have e : (2 ^ (10 * m)) ^ 5 = (q ^ 25) ^ 2 := by
      rw [hq, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
    rw [e]
    have := Nat.pow_lt_pow_left (hle.trans_lt hlt) (by norm_num : (2 : ℕ) ≠ 0)
    calc l3Num (p ^ f) b ^ 2 < (3 * q ^ 25) ^ 2 := this
      _ = 9 * (q ^ 25) ^ 2 := by ring

end

section

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Open (ordA ordTwistedA)

private theorem three_dvd_sq_sub_one {q : ℕ} (hq : q % 3 ≠ 0) : 3 ∣ q ^ 2 - 1 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine (Nat.modEq_iff_dvd' h1).mp ?_
  unfold Nat.ModEq
  rw [Nat.pow_mod]
  have : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases this with h | h <;> rw [h]

private theorem three_mul_ordA {q : ℕ} (hq : q % 3 = 1) : 3 * ordA 2 q = l3Num q false := by
  have hg : Nat.gcd 3 (q - 1) = 3 := Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
  have h3 : 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one (by omega)) _) _
  change 3 * (q ^ 3 * (∏ i ∈ Finset.Icc 2 3, (q ^ i - 1)) / Nat.gcd 3 (q - 1)) = _
  rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num), hg,
    Nat.mul_div_cancel' h3]
  simp [l3Num]

private theorem three_mul_ordTwistedA {q : ℕ} (hq : q % 3 = 2) : 3 * ordTwistedA 2 q = l3Num q true := by
  have hg : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
  have h3 : 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one (by omega)) _) _
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
    have : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]; ring
    rw [this, Int.toNat_natCast]
  have e3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  change 3 * (q ^ 3 * (∏ i ∈ Finset.Icc 2 3, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) /
    Nat.gcd 3 (q + 1)) = _
  rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num), e2, e3,
    hg, Nat.mul_div_cancel' h3]
  simp [l3Num]

private theorem center_eq_bot_of_factorization {X : Type} [Group X] [IsSimpleGroup X] {p f : ℕ}
    (hf : 1 ≤ f) (hX : Nat.card X ≠ 0) (h : (Nat.card X).factorization p = 3 * f) :
    center X = ⊥ := by
  have : Finite X := Nat.finite_of_card_ne_zero hX
  refine CFSG.RankThree.PartTwo.Sec21.Hering214.center_eq_bot_of_simple_of_not_prime
    inferInstance fun hp => ?_
  rw [hp.factorization, Finsupp.single_apply] at h
  split_ifs at h <;> omega

end

section

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Open (ordA ordTwistedA)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt IsSp4 IsG2 IsU5)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsSU5 IsSU5Four IsA6Z3 IsA7Z3 IsM22Z3 IsMathieu
  IsG2Der List880)

private theorem hundred_lt_l3Num {r : ℕ} (b : Bool) (hr : 4 ≤ r) : 100 < l3Num r b := by
  have h1 := l3Num_ge r b
  have a : 16 ≤ r ^ 2 := by nlinarith
  have c : 64 ≤ r ^ 3 := by nlinarith
  have : 64 * (15 * 63) ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) :=
    Nat.mul_le_mul c (Nat.mul_le_mul (by omega) (by omega))
  omega

private theorem sl3_side {X : Type} [Group X] (h : IsSL3PiType X) :
    ∃ (p f : ℕ) (b : Bool), p.Prime ∧ 1 ≤ f ∧ 4 ≤ p ^ f ∧
      ((Nat.card (center X) = 1 ∧ 3 * Nat.card X = l3Num (p ^ f) b ∧
          (b = false → LieModel X .PSL 3 p f)) ∨
        (Nat.card (center X) = 3 ∧ Nat.card X = l3Num (p ^ f) b)) := by
  rcases h with ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, -, hZ, h⟩ | ⟨p, f, hq, -, hZ, h⟩
  · have hp : p.Prime := h.admissible.1
    have hf : 1 ≤ f := h.admissible.2.1
    have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hc : 3 * Nat.card X = l3Num (p ^ f) false := by
      rw [h.card_eq_lieOrd (by norm_num)]; exact three_mul_ordA hq
    have hX : Nat.card X ≠ 0 := fun h0 => by
      have := hundred_lt_l3Num false (show 4 ≤ p ^ f by omega); omega
    have : IsSimpleGroup X :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    have hZ := center_eq_bot_of_factorization hf hX h.factorization_card_psl3
    exact ⟨p, f, false, hp, hf, by omega,
      Or.inl ⟨by rw [hZ]; exact Subgroup.card_bot, hc, fun _ => h⟩⟩
  · have hp : p.Prime := h.admissible.1
    have hf : 1 ≤ f := h.admissible.2.1
    have hne : (3, p ^ f) ≠ (3, 2) := h.admissible.2.2.2
    have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hq3 : p ^ f ≠ 2 := fun h2 => hne (by rw [h2])
    have hc : 3 * Nat.card X = l3Num (p ^ f) true := by
      rw [h.card_eq_lieOrd (by norm_num)]; exact three_mul_ordTwistedA hq
    have hX : Nat.card X ≠ 0 := fun h0 => by
      have := hundred_lt_l3Num true (show 4 ≤ p ^ f by omega); omega
    have : IsSimpleGroup X := CFSG.SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSU h
    have hZ := center_eq_bot_of_factorization hf hX h.factorization_card_psu3
    exact ⟨p, f, true, hp, hf, by omega,
      Or.inl ⟨by rw [hZ]; exact Subgroup.card_bot, hc, fun h => absurd h (by decide)⟩⟩
  · have hp : p.Prime := h.admissible.1
    have hf : 1 ≤ f := h.admissible.2.1
    have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hc : 3 * Nat.card (X ⧸ center X) = l3Num (p ^ f) false := by
      rw [h.card_eq_lieOrd (by norm_num)]; exact three_mul_ordA hq
    refine ⟨p, f, false, hp, hf, by omega, Or.inr ⟨hZ, ?_⟩⟩
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hZ, mul_comm]
    exact hc
  · have hp : p.Prime := h.admissible.1
    have hf : 1 ≤ f := h.admissible.2.1
    have hne : (3, p ^ f) ≠ (3, 2) := h.admissible.2.2.2
    have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hq3 : p ^ f ≠ 2 := fun h2 => hne (by rw [h2])
    have hc : 3 * Nat.card (X ⧸ center X) = l3Num (p ^ f) true := by
      rw [h.card_eq_lieOrd (by norm_num)]; exact three_mul_ordTwistedA hq
    refine ⟨p, f, true, hp, hf, by omega, Or.inr ⟨hZ, ?_⟩⟩
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hZ, mul_comm]
    exact hc

private def fixedOrders : List ℕ :=
  [7920, 95040, 443520, 10200960, 244823040, 604800, 44352000, 145926144000,
    86775571046077562880, 360, 2520, 20160, 9999360, 5616, 6048, 1080, 7560, 1330560]

private theorem fixed_small : ∀ r < 357, ∀ b : Bool, ∀ N ∈ fixedOrders, 4 ≤ r →
    (3 * N = l3Num r b → N = 20160 ∧ r = 4 ∧ b = false) ∧ N ≠ l3Num r b := by
  decide +kernel

private theorem fixed_large {N r : ℕ} (b : Bool) (hN : N ∈ fixedOrders) (hr : 357 ≤ r) :
    3 * N < l3Num r b := by
  have hNle : N ≤ 86775571046077562880 := by
    simp only [fixedOrders, List.mem_cons, List.not_mem_nil, or_false] at hN
    rcases hN with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  have hmono : 357 ^ 3 * ((357 ^ 2 - 1) * (357 ^ 3 - 1)) ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hr 3) (Nat.mul_le_mul
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hr 2) 1)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hr 3) 1))
  have := hmono.trans (l3Num_ge r b)
  norm_num at this
  omega

private theorem fixed_three {N r : ℕ} (b : Bool) (hN : N ∈ fixedOrders) (hr : 4 ≤ r)
    (h : 3 * N = l3Num r b) : N = 20160 ∧ r = 4 ∧ b = false := by
  by_cases hr' : r < 357
  · exact (fixed_small r hr' b N hN hr).1 h
  · have := fixed_large b hN (by omega : 357 ≤ r); omega

private theorem fixed_ne {N r : ℕ} (b : Bool) (hN : N ∈ fixedOrders) (hr : 4 ≤ r) : N ≠ l3Num r b := by
  by_cases hr' : r < 357
  · exact (fixed_small r hr' b N hN hr).2
  · have := fixed_large b hN (by omega : 357 ≤ r); omega

private theorem card_A6' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h
  have : (6 : ℕ).factorial = 720 := rfl
  omega

private theorem card_A7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin] at h
  have : (7 : ℕ).factorial = 5040 := rfl
  omega

private theorem card_A8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at h
  have : (8 : ℕ).factorial = 40320 := rfl
  omega

private theorem card_of_isAlt {X : Type} [Group X] {n : ℕ} (h : IsAlt X n) :
    Nat.card X = Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr e.toEquiv

private theorem card_sp4 {X : Type} [Group X] {n : ℕ} (h : LieModel X .PSp 2 2 n) :
    1 ≤ n ∧ Nat.card X = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
  have hn : 1 ≤ n := h.admissible.2.1
  refine ⟨hn, ?_⟩
  rw [h.card_eq_lieOrd (by norm_num)]
  have hodd : Odd (2 ^ n - 1) := by
    simpa using odd_two_pow_pow_sub_one hn (le_refl 1)
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd
  change (2 ^ n) ^ (2 * 2) * (∏ i ∈ Finset.Icc 1 2, ((2 ^ n) ^ (2 * i) - 1)) /
    Nat.gcd 2 (2 ^ n - 1) = _
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num), hg,
    Nat.div_one]

private theorem gcd_mul_ordTwistedA_four {q : ℕ} (hq : 1 ≤ q) :
    Nat.gcd 5 (q + 1) * ordTwistedA 4 q =
      q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have e2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
    have : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]; ring
    rw [this, Int.toNat_natCast]
  have e3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have e4 : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat = q ^ 4 - 1 := by
    have : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4) = ((q ^ 4 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h4]; ring
    rw [this, Int.toNat_natCast]
  have e5 : ((q : ℤ) ^ 5 - (-1 : ℤ) ^ 5).toNat = q ^ 5 + 1 := by
    have : ((q : ℤ) ^ 5 - (-1 : ℤ) ^ 5) = ((q ^ 5 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have h15 : q + 1 ∣ q ^ 5 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 5)
  have hdvd : Nat.gcd 5 (q + 1) ∣ q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left
      ((Nat.gcd_dvd_right 5 (q + 1)).trans h15) _) _) _) _
  change Nat.gcd 5 (q + 1) * (q ^ 10 * (∏ i ∈ Finset.Icc 2 5, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) /
    Nat.gcd 5 (q + 1)) = _
  rw [show Finset.Icc 2 5 = ({2, 3, 4, 5} : Finset ℕ) by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_pair (by norm_num), e2, e3, e4, e5,
    Nat.mul_div_cancel' hdvd]
  ring

private theorem not_simple_of_card_center_three {X : Type} [Group X] [IsSimpleGroup X]
    (h3 : Nat.card (center X) = 3) (hX : Nat.card X ≠ 3) : False := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · rw [h, Subgroup.card_bot] at h3; omega
  · rw [h, Subgroup.card_top] at h3; exact hX h3

theorem list880NotSL3PiType :
    List880NotSL3PiType := by
  intro X _ hL hS
  obtain ⟨p, f, b, hp, hf, hr4, hcase⟩ := sl3_side hS
  have hl := hundred_lt_l3Num b hr4
  have hX0 : Nat.card X ≠ 0 ∧ Nat.card X ≠ 3 := by
    rcases hcase with ⟨-, hc, -⟩ | ⟨-, hc⟩ <;> omega
  have : Finite X := Nat.finite_of_card_ne_zero hX0.1
  have hfix : ∀ N ∈ fixedOrders, Nat.card X = N →
      N = 20160 ∧ p ^ f = 4 ∧ LieModel X .PSL 3 p f := by
    intro N hN hX
    rcases hcase with ⟨-, hc, hL3⟩ | ⟨-, hc⟩
    · rw [hX] at hc
      obtain ⟨h1, h2, h3⟩ := fixed_three b hN hr4 hc
      exact ⟨h1, h2, hL3 h3⟩
    · rw [hX] at hc
      exact absurd hc (fixed_ne b hN hr4)
  have noFixed : ∀ N ∈ fixedOrders, N ≠ 20160 → Nat.card X ≠ N := fun N hN hne hX =>
    hne (hfix N hN hX).1
  have hspor : ∀ s : TauCeti.SporadicName, s ≠ .M →
      CFSG.AGLEmbeddingD2.d2SporadicOrder s ∈ fixedOrders →
      CFSG.AGLEmbeddingD2.d2SporadicOrder s ≠ 20160 → ¬ IsSpor X s := fun s hs hmem hne hX =>
    noFixed _ hmem hne
      (CFSG.GH74.card_eq_of_isSporadic (CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder s hs) hX)
  have hcover : ∀ N : ℕ, 3 * N ∈ fixedOrders → 3 * N ≠ 20160 → Nat.card (center X) = 3 →
      Nat.card (X ⧸ center X) = N → False := fun N hmem hne hZ hQ => by
    refine noFixed _ hmem hne ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hZ, hQ, mul_comm]
  rcases hL with ((h | h | h | h | h) | h | h | h | h | h | h | h | h | h | h | h | h | ⟨n, h⟩ | ⟨n, h⟩ |
      ⟨m, hm, h⟩ | h)
  · exact hspor .M11 (by decide) (by decide) (by decide) h
  · exact hspor .M12 (by decide) (by decide) (by decide) h
  · exact hspor .M22 (by decide) (by decide) (by decide) h
  · exact hspor .M23 (by decide) (by decide) (by decide) h
  · exact hspor .M24 (by decide) (by decide) (by decide) h
  · exact hspor .J2 (by decide) (by decide) (by decide) h
  · exact hspor .HS (by decide) (by decide) (by decide) h
  · exact hspor .Ru (by decide) (by decide) (by decide) h
  · exact hspor .J4 (by decide) (by decide) (by decide) h
  · obtain ⟨-, hZ, hA⟩ := h
    exact hcover 360 (by decide) (by decide) hZ ((card_of_isAlt hA).trans card_A6')
  · obtain ⟨-, hZ, hA⟩ := h
    exact hcover 2520 (by decide) (by decide) hZ ((card_of_isAlt hA).trans card_A7)
  · obtain ⟨-, hZ, hA⟩ := h
    exact hcover 443520 (by decide) (by decide) hZ (CFSG.GH74.card_eq_of_isSporadic
      (CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder .M22 (by decide)) hA)
  · exact noFixed 360 (by decide) (by decide) ((card_of_isAlt h).trans card_A6')
  · exact noFixed 2520 (by decide) (by decide) ((card_of_isAlt h).trans card_A7)
  ·
    obtain ⟨-, h4, hL3⟩ := hfix 20160 (by decide) ((card_of_isAlt h).trans card_A8)
    have hp2 : p = 2 := by
      have : p ∣ 2 ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = 4 from rfl, ← h4]; exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst hp2
    have hf2 : f = 2 := Nat.pow_right_injective (le_refl 2) (h4.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
    subst hf2
    obtain ⟨e⟩ := h
    exact ((CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated X
      (hL3.statedClassicalModel_of_ne_zero (by norm_num))).2.2 (Fin 8) (by simp)).false e
  · exact noFixed 9999360 (by decide) (by decide) ((h.card_eq_lieOrd (by norm_num)).trans (by decide))
  · exact noFixed 5616 (by decide) (by decide) ((h.card_eq_lieOrd (by norm_num)).trans (by decide))
  ·
    obtain ⟨hn, hcard⟩ := card_sp4 h
    rcases hcase with ⟨-, hc, -⟩ | ⟨hZ, -⟩
    · exact three_mul_sp4_ne_l3Num b hn hp hr4 (hcard ▸ hc)
    · have : IsSimpleGroup X :=
        CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
      exact not_simple_of_card_center_three hZ hX0.2
  ·
    rcases h with ⟨-, h⟩ | ⟨hn, h⟩
    · exact noFixed 6048 (by decide) (by decide) ((h.card_eq_lieOrd (by norm_num)).trans (by decide))
    · have hcard := CFSG.EvenSporadicStandard.Induction.card_of_lieModel_g_two n h
      rcases hcase with ⟨-, hc, -⟩ | ⟨hZ, -⟩
      · refine three_mul_g2_ne_l3Num (n := n) b (by omega) hp hr4 ?_
        rw [← hc, hcard, CFSG.Open.ordG2, mul_assoc]
      · have : IsSimpleGroup X := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_lieModel_isSimple_G2 h
        exact not_simple_of_card_center_three hZ hX0.2
  ·
    rcases hcase with ⟨hZ, hc, -⟩ | ⟨hZ, -⟩
    · have hQ : Nat.card X = Nat.card (X ⧸ center X) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hZ, mul_one]
      have hU : LieModel (X ⧸ center X) .PSU 5 2 m := h.2
      have hid := gcd_mul_ordTwistedA_four (q := 2 ^ m) (Nat.one_le_two_pow)
      have hcQ : Nat.card (X ⧸ center X) = ordTwistedA 4 (2 ^ m) := hU.card_eq_lieOrd (by norm_num)
      rw [← hcQ] at hid
      refine three_mul_u5_ne_l3Num (m := m) b (by omega) hp hr4 ?_
      rw [← hid, ← hc, hQ]
      ring
    · exact not_three_dvd_card_center_of_isSU5 h (by rw [hZ])
  ·
    obtain ⟨-, h5⟩ := h
    rcases hcase with ⟨hZ, -⟩ | ⟨hZ, -⟩ <;> omega

end

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
