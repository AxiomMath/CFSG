module

public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinDefs
public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinForms
import CFSG.GH74.GLS.Stage2.Final.ModelArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.GH74.GLS.Stage2.Final.ModelArith

private lemma w183art_prod_Icc_le (q n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) ≤ q ^ (n * (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (show 1 ≤ n + 1 by omega)]
    calc (∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)) * (q ^ (2 * (n + 1)) - 1)
        ≤ q ^ (n * (n + 1)) * q ^ (2 * (n + 1)) :=
          Nat.mul_le_mul ih (Nat.sub_le _ _)
      _ = q ^ ((n + 1) * (n + 2)) := by
          rw [← pow_add]
          congr 1
          ring

theorem w183art_pow_dvd_of_mul_eq {q N C d M : ℕ} (hodd : Odd q) (hd : d ∣ 4)
    (h : M * d = q ^ N * C) : q ^ N ∣ M := by
  have hc2 : q.Coprime 2 := Nat.coprime_two_right.2 hodd
  have hc4 : q.Coprime 4 := by
    simpa using hc2.pow_right 2
  have hcd : q.Coprime d := hc4.coprime_dvd_right hd
  have hcop : (q ^ N).Coprime d := hcd.pow_left N
  exact hcop.dvd_of_dvd_mul_right ⟨C, h⟩

theorem w183art_sq_lt_of_mul_eq {q N C d M : ℕ} (hd : 2 ≤ d) (h : M * d = q ^ N * C)
    (hC : C ^ 2 < 4 * q ^ (3 * N)) : M ^ 2 < (q ^ N) ^ 5 := by
  have hqNpos : 0 < q ^ N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hqpos : 0 < q := by
        rcases Nat.eq_zero_or_pos q with rfl | hq
        · rw [zero_pow (show 3 * N ≠ 0 by omega)] at hC
          omega
        · exact hq
      exact pow_pos hqpos N
  have hqN2pos : 0 < (q ^ N) ^ 2 := pow_pos hqNpos 2
  have h2M : 2 * M ≤ M * d := by
    calc 2 * M = M * 2 := mul_comm 2 M
      _ ≤ M * d := Nat.mul_le_mul_left M hd
  have h1 : (2 * M) ^ 2 ≤ (M * d) ^ 2 := Nat.pow_le_pow_left h2M 2
  have h2 : (M * d) ^ 2 = (q ^ N) ^ 2 * C ^ 2 := by rw [h, mul_pow]
  have h3 : (q ^ N) ^ 2 * C ^ 2 < (q ^ N) ^ 2 * (4 * q ^ (3 * N)) :=
    Nat.mul_lt_mul_of_pos_left hC hqN2pos
  have h4 : (q ^ N) ^ 2 * (4 * q ^ (3 * N)) = 4 * (q ^ N) ^ 5 := by
    calc (q ^ N) ^ 2 * (4 * q ^ (3 * N))
        = 4 * ((q ^ N) ^ 2 * q ^ (3 * N)) := by ring
      _ = 4 * (q ^ (N * 2) * q ^ (3 * N)) := by rw [← pow_mul]
      _ = 4 * q ^ (N * 2 + 3 * N) := by rw [pow_add]
      _ = 4 * q ^ (N * 5) := by congr 1; ring
      _ = 4 * (q ^ N) ^ 5 := by rw [pow_mul]
  have hchain : (2 * M) ^ 2 < 4 * (q ^ N) ^ 5 := by
    rw [h2] at h1
    exact lt_of_le_of_lt h1 (h3.trans_eq h4)
  have h5 : (2 * M) ^ 2 = 4 * M ^ 2 := by ring
  rw [h5] at hchain
  omega

theorem w183art_big_ordBC {q n : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (hn : 2 ≤ n) :
    ArtinBig q (ordBC n q) := by
  have hn1 : 1 ≤ n := by omega
  have h2q : 2 ∣ q - 1 := by
    rcases hodd with ⟨k, rfl⟩
    exact ⟨k, by omega⟩
  set d : ℕ := Nat.gcd 2 (q - 1) with hddef
  set C : ℕ := ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) with hCdef
  have h : ordBC n q * d = q ^ (n * n) * C := by
    rw [mul_comm (ordBC n q) d, hddef, hCdef]
    exact w183art_gcd_mul_ordBC (q := q) hn1
  have hd_eq : d = 2 := by rw [hddef]; exact Nat.gcd_eq_left h2q
  have hd : d ∣ 4 := by rw [hd_eq]; norm_num
  have hd2 : 2 ≤ d := by rw [hd_eq]
  have hCbound : C ≤ q ^ (n * (n + 1)) := by
    rw [hCdef]; exact w183art_prod_Icc_le q n
  have hC2 : C ^ 2 ≤ q ^ (2 * (n * (n + 1))) := by
    calc C ^ 2 ≤ (q ^ (n * (n + 1))) ^ 2 := Nat.pow_le_pow_left hCbound 2
      _ = q ^ (2 * (n * (n + 1))) := by rw [← pow_mul]; congr 1; ring
  have hexp : 2 * (n * (n + 1)) ≤ 3 * (n * n) := by nlinarith [hn]
  have hC2' : C ^ 2 ≤ q ^ (3 * (n * n)) :=
    hC2.trans (Nat.pow_le_pow_right (by omega) hexp)
  have hC : C ^ 2 < 4 * q ^ (3 * (n * n)) := by
    have hpos : 0 < q ^ (3 * (n * n)) := pow_pos (by omega) _
    nlinarith
  exact ⟨n * n, w183art_pow_dvd_of_mul_eq hodd hd h, w183art_sq_lt_of_mul_eq hd2 h hC⟩

theorem w183art_big_ordA_three {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) : ArtinBig q (ordA 3 q) := by
  have h2q : 2 ∣ q - 1 := by
    rcases hodd with ⟨k, rfl⟩
    exact ⟨k, by omega⟩
  set d : ℕ := Nat.gcd 4 (q - 1) with hddef
  set C : ℕ := (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) with hCdef
  have h : ordA 3 q * d = q ^ 6 * C := by
    rw [mul_comm (ordA 3 q) d, hddef, hCdef]
    exact gcd_mul_ordA_three (q := q)
  have hd : d ∣ 4 := by rw [hddef]; exact Nat.gcd_dvd_left 4 (q - 1)
  have h2dvd : 2 ∣ d := by
    rw [hddef]
    exact Nat.dvd_gcd (by norm_num) h2q
  have hd2 : 2 ≤ d := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd (by norm_num)) h2dvd
  have hY : C < 2 * q ^ 9 := by rw [hCdef]; exact Y_lt_L (by omega)
  have hCsq : C ^ 2 < (2 * q ^ 9) ^ 2 := by
    have h1 : C * C < (2 * q ^ 9) * (2 * q ^ 9) := Nat.mul_lt_mul'' hY hY
    simpa only [pow_two] using h1
  have hC : C ^ 2 < 4 * q ^ (3 * 6) := by
    calc C ^ 2 < (2 * q ^ 9) ^ 2 := hCsq
      _ = 4 * q ^ 18 := by rw [mul_pow, ← pow_mul]; norm_num
      _ = 4 * q ^ (3 * 6) := by norm_num
  exact ⟨6, w183art_pow_dvd_of_mul_eq hodd hd h, w183art_sq_lt_of_mul_eq hd2 h hC⟩

theorem w183art_big_ordTwistedA_three {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) :
    ArtinBig q (ordTwistedA 3 q) := by
  have h2q : 2 ∣ q + 1 := by
    rcases hodd with ⟨k, rfl⟩
    exact ⟨k + 1, by omega⟩
  set d : ℕ := Nat.gcd 4 (q + 1) with hddef
  set C : ℕ := (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) with hCdef
  have h : ordTwistedA 3 q * d = q ^ 6 * C := by
    rw [mul_comm (ordTwistedA 3 q) d, hddef, hCdef]
    exact gcd_mul_ordTwistedA_three (q := q)
  have hd : d ∣ 4 := by rw [hddef]; exact Nat.gcd_dvd_left 4 (q + 1)
  have h2dvd : 2 ∣ d := by
    rw [hddef]
    exact Nat.dvd_gcd (by norm_num) h2q
  have hd2 : 2 ≤ d := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd (by norm_num)) h2dvd
  have hY : C < 2 * q ^ 9 := by rw [hCdef]; exact Y_lt_U (by omega)
  have hCsq : C ^ 2 < (2 * q ^ 9) ^ 2 := by
    have h1 : C * C < (2 * q ^ 9) * (2 * q ^ 9) := Nat.mul_lt_mul'' hY hY
    simpa only [pow_two] using h1
  have hC : C ^ 2 < 4 * q ^ (3 * 6) := by
    calc C ^ 2 < (2 * q ^ 9) ^ 2 := hCsq
      _ = 4 * q ^ 18 := by rw [mul_pow, ← pow_mul]; norm_num
      _ = 4 * q ^ (3 * 6) := by norm_num
  exact ⟨6, w183art_pow_dvd_of_mul_eq hodd hd h, w183art_sq_lt_of_mul_eq hd2 h hC⟩

theorem w183art_big_ordD {q n : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (hn : 4 ≤ n) :
    ArtinBig q (ordD n q) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  set d : ℕ := Nat.gcd 4 (q ^ (m + 4) - 1) with hddef
  set P : ℕ := ∏ i ∈ Finset.Icc 1 (m + 3), (q ^ (2 * i) - 1) with hPdef
  set C : ℕ := (q ^ (m + 4) - 1) * P with hCdef
  have h : ordD (m + 4) q * d = q ^ ((m + 4) * (m + 3)) * C := by
    rw [mul_comm (ordD (m + 4) q) d, hddef, hCdef, hPdef]
    exact w183art_gcd_mul_ordD (n := m + 4) (q := q) (by omega)
  have h2qn : 2 ∣ q ^ (m + 4) - 1 :=
    (Nat.Odd.sub_odd hodd.pow odd_one).two_dvd
  have hd : d ∣ 4 := by rw [hddef]; exact Nat.gcd_dvd_left 4 (q ^ (m + 4) - 1)
  have h2dvd : 2 ∣ d := by
    rw [hddef]
    exact Nat.dvd_gcd (by norm_num) h2qn
  have hd2 : 2 ≤ d := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd (by norm_num)) h2dvd
  have hPbound : P ≤ q ^ ((m + 3) * ((m + 3) + 1)) := by
    rw [hPdef]; exact w183art_prod_Icc_le q (m + 3)
  have hCbound : C ≤ q ^ ((m + 4) * (m + 4)) := by
    rw [hCdef]
    calc (q ^ (m + 4) - 1) * P
        ≤ q ^ (m + 4) * q ^ ((m + 3) * ((m + 3) + 1)) :=
          Nat.mul_le_mul (Nat.sub_le _ _) hPbound
      _ = q ^ ((m + 4) * (m + 4)) := by
          rw [← pow_add,
            show (m + 4) + (m + 3) * ((m + 3) + 1) = (m + 4) * (m + 4) by ring]
  have hC2 : C ^ 2 ≤ q ^ (2 * ((m + 4) * (m + 4))) := by
    calc C ^ 2 ≤ (q ^ ((m + 4) * (m + 4))) ^ 2 := Nat.pow_le_pow_left hCbound 2
      _ = q ^ (2 * ((m + 4) * (m + 4))) := by rw [← pow_mul]; congr 1; ring
  have hexp : 2 * ((m + 4) * (m + 4)) < 3 * ((m + 4) * (m + 3)) := by nlinarith
  have hC' : C ^ 2 < q ^ (3 * ((m + 4) * (m + 3))) :=
    lt_of_le_of_lt hC2 (Nat.pow_lt_pow_right (by omega : 1 < q) hexp)
  have hC : C ^ 2 < 4 * q ^ (3 * ((m + 4) * (m + 3))) := by
    have hpos : 0 < q ^ (3 * ((m + 4) * (m + 3))) := pow_pos (by omega) _
    nlinarith
  exact ⟨(m + 4) * (m + 3),
    w183art_pow_dvd_of_mul_eq hodd hd h, w183art_sq_lt_of_mul_eq hd2 h hC⟩

theorem w183art_big_ordTwistedD {q n : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (hn : 4 ≤ n) :
    ArtinBig q (ordTwistedD n q) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  set d : ℕ := Nat.gcd 4 (q ^ (m + 4) + 1) with hddef
  set P : ℕ := ∏ i ∈ Finset.Icc 1 (m + 3), (q ^ (2 * i) - 1) with hPdef
  set C : ℕ := (q ^ (m + 4) + 1) * P with hCdef
  have h : ordTwistedD (m + 4) q * d = q ^ ((m + 4) * (m + 3)) * C := by
    rw [mul_comm (ordTwistedD (m + 4) q) d, hddef, hCdef, hPdef]
    exact w183art_gcd_mul_ordTwistedD (n := m + 4) (q := q) (by omega)
  have h2qn : 2 ∣ q ^ (m + 4) + 1 := (Odd.add_odd hodd.pow odd_one).two_dvd
  have hd : d ∣ 4 := by rw [hddef]; exact Nat.gcd_dvd_left 4 (q ^ (m + 4) + 1)
  have h2dvd : 2 ∣ d := by
    rw [hddef]
    exact Nat.dvd_gcd (by norm_num) h2qn
  have hd2 : 2 ≤ d := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd (by norm_num)) h2dvd
  have hPbound : P ≤ q ^ ((m + 3) * ((m + 3) + 1)) := by
    rw [hPdef]; exact w183art_prod_Icc_le q (m + 3)
  have hqp : q ^ (m + 4) + 1 ≤ 2 * q ^ (m + 4) := by
    have h1 : 1 ≤ q ^ (m + 4) := Nat.one_le_pow _ _ (by omega)
    omega
  have hCbound : C ≤ 2 * q ^ ((m + 4) * (m + 4)) := by
    rw [hCdef]
    calc (q ^ (m + 4) + 1) * P
        ≤ (2 * q ^ (m + 4)) * q ^ ((m + 3) * ((m + 3) + 1)) :=
          Nat.mul_le_mul hqp hPbound
      _ = 2 * q ^ ((m + 4) * (m + 4)) := by
          rw [mul_assoc, ← pow_add,
            show (m + 4) + (m + 3) * ((m + 3) + 1) = (m + 4) * (m + 4) by ring]
  have hC2 : C ^ 2 ≤ 4 * q ^ (2 * ((m + 4) * (m + 4))) := by
    calc C ^ 2 ≤ (2 * q ^ ((m + 4) * (m + 4))) ^ 2 := Nat.pow_le_pow_left hCbound 2
      _ = 4 * q ^ (2 * ((m + 4) * (m + 4))) := by
          rw [mul_pow, ← pow_mul,
            show (m + 4) * (m + 4) * 2 = 2 * ((m + 4) * (m + 4)) by ring]
          norm_num
  have hexp : 2 * ((m + 4) * (m + 4)) < 3 * ((m + 4) * (m + 3)) := by nlinarith
  have hC3 : 4 * q ^ (2 * ((m + 4) * (m + 4))) <
      4 * q ^ (3 * ((m + 4) * (m + 3))) :=
    Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by omega : 1 < q) hexp) (by norm_num)
  have hC : C ^ 2 < 4 * q ^ (3 * ((m + 4) * (m + 3))) := hC2.trans_lt hC3
  exact ⟨(m + 4) * (m + 3),
    w183art_pow_dvd_of_mul_eq hodd hd h, w183art_sq_lt_of_mul_eq hd2 h hC⟩

end CFSG.LocalAnalysis.WeakClosure81
