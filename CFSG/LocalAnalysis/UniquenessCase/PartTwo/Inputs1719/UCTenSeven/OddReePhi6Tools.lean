module

public import CFSG.Walter.ReeOrder.JT.Defs
public import CFSG.Walter.ReeOrder.Ward.Defs
import CFSG.Walter.ReeOrder.Ward.Order
import CFSG.Walter.AStar.Basic
import CFSG.Walter.ReeOrder.JT.Section4I
import CFSG.Walter.ReeOrder.JT.Section7ZB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped MatrixGroups

theorem phi6_torus_not_dvd {k n : ℕ} (hk : 1 ≤ k)
    (hn : n = 3 ^ (2 * k + 1) + 1 + 3 ^ (k + 1) ∨ n + 3 ^ (k + 1) = 3 ^ (2 * k + 1) + 1) :
    ¬ n ∣ 168 := by
  have fin : n % 2 = 1 → n % 3 = 1 → 19 ≤ n → n ∣ 168 → False := by
    intro h2 h3 h19 hd
    have hodd : Odd n := Nat.odd_iff.mpr h2
    have hcop : Nat.Coprime n (2 ^ 3) := hodd.coprime_two_right.pow_right 3
    have h168 : 168 = 2 ^ 3 * 21 := by norm_num
    have hd21 : n ∣ 21 := by
      apply Nat.Coprime.dvd_of_dvd_mul_left hcop
      rwa [← h168]
    have hle21 : n ≤ 21 := Nat.le_of_dvd (by norm_num) hd21
    interval_cases n <;> norm_num at *
  intro hdvd
  have ha2 : 3 ^ k % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  obtain ⟨c, hc⟩ : ∃ c, 3 ^ k = 2 * c + 1 := Nat.odd_iff.mpr ha2
  have hc1 : 1 ≤ c := by
    have ha3 : 3 ≤ 3 ^ k := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 3) hk
    omega
  have h2k : 3 ^ (2 * k + 1) = 3 * (3 ^ k) ^ 2 := by
    have h : 3 ^ (2 * k) = (3 ^ k) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    rw [pow_succ, h]; ring
  have hk1 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
  rcases hn with hn | hn
  · have hEq : n = 2 * (6 * c ^ 2 + 9 * c + 3) + 1 := by rw [hn, h2k, hk1, hc]; ring
    have hn19 : 19 ≤ n := by rw [hEq]; nlinarith
    have hn2 : n % 2 = 1 := by rw [hEq]; omega
    have hn3 : n % 3 = 1 := by
      have h3 : n = 3 * (4 * c ^ 2 + 6 * c + 2) + 1 := by rw [hEq]; ring
      rw [h3]; omega
    exact fin hn2 hn3 hn19 hdvd
  · have h3' : n + 3 * (3 ^ k) = 3 * (3 ^ k) ^ 2 + 1 := by rw [← hk1, ← h2k]; exact hn
    have hEq : n = 2 * (6 * c ^ 2 + 3 * c) + 1 := by
      have h4 : n + 3 * (3 ^ k) = (2 * (6 * c ^ 2 + 3 * c) + 1) + 3 * (3 ^ k) := by
        rw [h3', hc]; ring
      exact Nat.add_right_cancel h4
    have hn19 : 19 ≤ n := by rw [hEq]; nlinarith
    have hn2 : n % 2 = 1 := by rw [hEq]; omega
    have hn3 : n % 3 = 1 := by
      have h3 : n = 3 * (4 * c ^ 2 + 2 * c) + 1 := by rw [hEq]; ring
      rw [h3]; omega
    exact fin hn2 hn3 hn19 hdvd

private lemma sq_three (k : ℕ) : (3 ^ (k + 1)) ^ 2 = 3 * 3 ^ (2 * k + 1) := by
  have h1 : (3 ^ (k + 1)) ^ 2 = 3 ^ ((k + 1) * 2) := by rw [pow_mul]
  have h2 : 3 * 3 ^ (2 * k + 1) = 3 ^ (2 * k + 1 + 1) := by rw [pow_succ]; ring
  rw [h1, h2]
  congr 1
  omega

private lemma phi6_mul {q s : ℕ} (hq : 1 ≤ q) (hs2 : s ^ 2 = 3 * q) :
    (q + 1 + s) * (q + 1 - s) = q ^ 2 - q + 1 := by
  rw [← Nat.sq_sub_sq (q + 1) s]
  have h1 : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
  rw [h1, hs2]
  have hle : 3 * q ≤ (q + 1) ^ 2 := by nlinarith
  have hqle : q ≤ q ^ 2 := by nlinarith
  omega

theorem phi6_torus_eq_of_dvd {k m n : ℕ} (hk : 1 ≤ k) (hm3 : 3 ≤ m) (hm : m ∣ 2 * k + 1)
    (hn : n = 3 ^ (2 * k + 1) + 1 + 3 ^ (k + 1) ∨ n + 3 ^ (k + 1) = 3 ^ (2 * k + 1) + 1)
    (hdvd : n ∣ (3 ^ m) ^ 3 * ((3 ^ m) ^ 3 + 1) * (3 ^ m - 1)) : m = 2 * k + 1 := by
  obtain ⟨j, hj⟩ : ∃ j, 2 * k + 1 = m * j := hm
  set q : ℕ := 3 ^ (2 * k + 1) with hq
  set s : ℕ := 3 ^ (k + 1) with hs
  have hs2 : s ^ 2 = 3 * q := by rw [hq, hs]; exact sq_three k
  have hq27 : 27 ≤ q := by
    rw [hq]
    calc 27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : 1 ≤ q := by omega
  have hs0 : 0 < s := by positivity
  have hq3mod : q % 3 = 0 := by rw [hq, Nat.pow_mod]; norm_num
  have hs3mod : s % 3 = 0 := by rw [hs, Nat.pow_mod]; norm_num
  have hn3mod : n % 3 = 1 := by
    rcases hn with hn | hn
    · rw [hn]; omega
    · omega
  have h3n : ¬ 3 ∣ n := by
    intro hd
    have := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  have hnA : n ∣ ((3 ^ m) ^ 3 + 1) * (3 ^ m - 1) := by
    have h3m : (3 ^ m) ^ 3 = 3 ^ (3 * m) := by rw [← pow_mul, Nat.mul_comm]
    have hcop3 : Nat.Coprime n (3 ^ (3 * m)) := Nat.prime_three.coprime_pow_of_not_dvd h3n
    have hcop3' : Nat.Coprime n ((3 ^ m) ^ 3) := by rwa [← h3m] at hcop3
    apply Nat.Coprime.dvd_of_dvd_mul_left hcop3'
    have h : n ∣ (3 ^ m) ^ 3 * (((3 ^ m) ^ 3 + 1) * (3 ^ m - 1)) := by
      rw [mul_assoc] at hdvd
      exact hdvd
    exact h
  have h2sq : 2 * s ≤ q := by
    have h4 : (2 * s) ^ 2 ≤ q ^ 2 := by
      have h5 : (2 * s) ^ 2 = 4 * (s ^ 2) := by ring
      rw [h5, hs2]
      have h6 : 12 ≤ q := by omega
      nlinarith
    have h7 : (2 * s) * (2 * s) ≤ q * q := by
      simpa [pow_two] using h4
    exact Nat.mul_self_le_mul_self_iff.mp h7
  clear hq3mod hs3mod
  rcases j with _ | _ | _ | _ | j
  · omega
  · omega
  · omega
  ·
    have hq3 : q = (3 ^ m) ^ 3 := by rw [hq, hj, ← pow_mul]
    have hnB : n ∣ q ^ 2 - q + 1 := by
      rcases hn with hn | hn
      · rw [hn]
        exact ⟨q + 1 - s, by rw [phi6_mul hq1 hs2]⟩
      · rw [show n = q + 1 - s by omega]
        exact ⟨q + 1 + s, by rw [mul_comm, phi6_mul hq1 hs2]⟩
    have hnB' : n ∣ (3 ^ m) ^ 6 - (3 ^ m) ^ 3 + 1 := by
      have h := hnB
      rw [hq3, ← pow_mul] at h
      norm_num at h
      exact h
    have hcube : (3 ^ m - 1) ∣ (3 ^ m) ^ 3 - 1 := by
      have h3 : (3 ^ m - 1) * ((3 ^ m) ^ 2 + 3 ^ m + 1) = (3 ^ m) ^ 3 - 1 := by
        rw [Nat.sub_mul, one_mul]
        have h4 : (3 ^ m) * ((3 ^ m) ^ 2 + 3 ^ m + 1) = (3 ^ m) ^ 3 + (3 ^ m) ^ 2 + 3 ^ m := by ring
        rw [h4]
        have h5 : 1 ≤ (3 ^ m) ^ 3 := by
          have : 0 < 3 ^ m := by positivity
          nlinarith
        omega
      exact ⟨_, h3.symm⟩
    have hg : Nat.gcd n (3 ^ m - 1) = 1 := by
      set g := Nat.gcd n (3 ^ m - 1) with hg'
      have hgn : g ∣ n := by rw [hg']; exact Nat.gcd_dvd_left ..
      have hgr : g ∣ 3 ^ m - 1 := by rw [hg']; exact Nat.gcd_dvd_right ..
      have hgB : g ∣ (3 ^ m) ^ 6 - (3 ^ m) ^ 3 + 1 := hgn.trans hnB'
      have hg63 : g ∣ (3 ^ m) ^ 6 - (3 ^ m) ^ 3 := by
        have hsplit : (3 ^ m) ^ 6 - (3 ^ m) ^ 3 = (3 ^ m) ^ 3 * ((3 ^ m) ^ 3 - 1) := by
          rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add]
        rw [hsplit]
        exact Dvd.dvd.mul_left (hgr.trans hcube) _
      have hone : g ∣ 1 := by
        have h := Nat.dvd_sub hgB hg63
        simpa using h
      exact Nat.dvd_one.mp hone
    have hcopm : Nat.Coprime n (3 ^ m - 1) := hg
    have hnF : n ∣ (3 ^ m) ^ 3 + 1 := by
      apply Nat.Coprime.dvd_of_dvd_mul_left hcopm
      rwa [mul_comm] at hnA
    have hleF : n ≤ (3 ^ m) ^ 3 + 1 := Nat.le_of_dvd (by positivity) hnF
    have hsle : s ≤ (3 ^ m) ^ 3 + 1 := by
      rw [← hq3]
      exact Nat.le_succ_of_le (Nat.mul_self_le_mul_self_iff.mp (by
        rw [pow_two] at hs2
        have h3q : 3 ≤ q := by omega
        calc s * s = 3 * q := hs2
          _ ≤ q * q := Nat.mul_le_mul_right q h3q))
    clear hnB hnB' hcube hg hcopm h3n hnA
    rcases hn with hn | hn
    · have hgt : (3 ^ m) ^ 3 + 1 < n := by
        rw [hn, hq3]
        exact Nat.lt_add_of_pos_right hs0
      exact absurd hgt (not_lt_of_ge hleF)
    · have hnEq : n = (3 ^ m) ^ 3 + 1 - s := by
        have h1 : n = (n + s) - s := (Nat.add_sub_cancel_right n s).symm
        rw [h1, hn, hq3]
      have hsub : (3 ^ m) ^ 3 + 1 - n = s := by
        rw [hnEq]
        exact Nat.sub_sub_self hsle
      have hdvdn : n ∣ s := by
        have h := Nat.dvd_sub hnF (dvd_refl n)
        rwa [hsub] at h
      have hsn : s < n := by
        rw [hnEq]
        omega
      exact absurd hsn (not_lt_of_ge (Nat.le_of_dvd hs0 hdvdn))
  · rcases j with _ | j
    · omega
    ·
      have hr27 : 27 ≤ 3 ^ m := by
        calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
      have hqj : q = (3 ^ m) ^ (j + 5) := by rw [hq, hj, ← pow_mul]
      have hq_big : 27 * (3 ^ m) ^ 4 ≤ q := by
        have h1 : (3 ^ m) ^ 5 ≤ (3 ^ m) ^ (j + 5) :=
          Nat.pow_le_pow_right (by positivity) (by omega)
        have h2 : 27 * (3 ^ m) ^ 4 ≤ (3 ^ m) ^ 5 := by
          rw [show (3 ^ m) ^ 5 = (3 ^ m) * (3 ^ m) ^ 4 by rw [pow_succ']]
          exact Nat.mul_le_mul_right _ hr27
        rw [hqj]
        exact le_trans h2 h1
      have h2n : q < 2 * n := by
        rcases hn with hn | hn
        · rw [hn]; omega
        · omega
      have hn_big : (3 ^ m) ^ 4 < n := by
        have h2 : 2 * (3 ^ m) ^ 4 ≤ 27 * (3 ^ m) ^ 4 :=
          Nat.mul_le_mul_right _ (by norm_num)
        omega
      have hprod_lt : ((3 ^ m) ^ 3 + 1) * (3 ^ m - 1) < (3 ^ m) ^ 4 := by
        have hX : 1 ≤ 3 ^ m := by
          have h : 0 < 3 ^ m := by positivity
          omega
        have h34 : (3 ^ m) ^ 3 ≤ (3 ^ m) ^ 4 :=
          Nat.pow_le_pow_right (by positivity) (by norm_num)
        have hX3 : 3 ^ m ≤ (3 ^ m) ^ 3 := by
          calc 3 ^ m = (3 ^ m) ^ 1 := (pow_one _).symm
          _ ≤ (3 ^ m) ^ 3 := Nat.pow_le_pow_right (by positivity) (by norm_num)
        have hkey : ((3 ^ m) ^ 3 + 1) * (3 ^ m - 1) =
            ((3 ^ m) ^ 4 - (3 ^ m) ^ 3) + ((3 ^ m) - 1) := by
          rw [Nat.add_mul, one_mul, Nat.mul_sub_left_distrib, mul_one, ← pow_succ]
        rw [hkey]
        omega
      have hpos : 0 < ((3 ^ m) ^ 3 + 1) * (3 ^ m - 1) := by
        have h3m : 1 < 3 ^ m := by
          have h : 3 ^ 1 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h' : (3 : ℕ) ≤ 3 ^ m := by simpa using h
          omega
        have h1 : 0 < (3 ^ m) ^ 3 + 1 := by positivity
        have h2 : 0 < 3 ^ m - 1 := by omega
        exact Nat.mul_pos h1 h2
      have hle := Nat.le_of_dvd hpos hnA
      omega

private lemma nine_pow_mod_eight (i : ℕ) : 9 ^ i % 8 = 1 := by
  rw [Nat.pow_mod]
  norm_num

private lemma eight_one_pow_mod_sixteen (i : ℕ) : 81 ^ i % 16 = 1 := by
  rw [Nat.pow_mod]
  norm_num

private lemma eight_one_pow_mod_five (i : ℕ) : 81 ^ i % 5 = 1 := by
  rw [Nat.pow_mod]
  norm_num

theorem psl2_three_subgroup_cases {p f : ℕ} [Fact p.Prime]
    (hp3 : p = 3) (hf : Odd f) (R : Subgroup PSL(2, GaloisField p f)) (h12 : 12 ∣ Nat.card R) :
    Nat.card R = 12 ∨ ∃ m : ℕ, 3 ≤ m ∧ m ∣ f ∧ Nonempty (R ≃* PSL(2, GaloisField p m)) := by
  subst hp3
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hf
    omega
  have hFcard : Nat.card (GaloisField 3 f) = 3 ^ f := GaloisField.card 3 f hf0
  have h4 : 4 ∣ Nat.card R := Nat.dvd_trans (by norm_num) h12
  have h2 : 2 ∣ Nat.card R := Nat.dvd_trans (by norm_num) h4
  have hq8 : 3 ^ f % 8 = 3 := by
    obtain ⟨i, rfl⟩ := hf
    have h : 3 ^ (2 * i + 1) = 9 ^ i * 3 := by rw [pow_succ, pow_mul]; norm_num
    rw [h, Nat.mul_mod, nine_pow_mod_eight]
  have h9_16 : 9 ^ f % 16 = 9 := by
    obtain ⟨i, rfl⟩ := hf
    have h : 9 ^ (2 * i + 1) = 81 ^ i * 9 := by rw [pow_succ, pow_mul]; norm_num
    rw [h, Nat.mul_mod, eight_one_pow_mod_sixteen]
  have h9_5 : 9 ^ f % 5 = 4 := by
    obtain ⟨i, rfl⟩ := hf
    have h : 9 ^ (2 * i + 1) = 81 ^ i * 9 := by rw [pow_succ, pow_mul]; norm_num
    rw [h, Nat.mul_mod, eight_one_pow_mod_five]
  have hqodd : 3 ^ f % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2d1 : 2 ∣ 3 ^ f - 1 := by omega
  have h2d2 : 2 ∣ 3 ^ f + 1 := by omega
  have hgcd : (3 ^ f - 1).gcd 2 = 2 := by
    rw [Nat.gcd_eq_right]
    omega
  have h2pow : 3 ^ (2 * f) = 9 ^ f := by rw [pow_mul]; norm_num
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
    (F := GaloisField 3 f) hFcard R with
    h1 | h2' | h3 | h4' | h5 | h6 | h7 | h8 | h9
  ·
    obtain ⟨m, hm⟩ := h1.isPGroup.exists_card_eq
    rw [hm, Nat.dvd_iff_mod_eq_zero, Nat.pow_mod] at h2
    norm_num at h2
  ·
    obtain ⟨z, hzdiv, hzcard, hzcyc⟩ := h2'
    have h4z : 4 ∣ z := by rw [← hzcard]; exact h4
    rw [hFcard] at hzdiv
    rw [hgcd] at hzdiv
    rcases hzdiv with hz | hz
    · have h8 : 8 ∣ 3 ^ f - 1 := by
        obtain ⟨k, hk⟩ := h4z.trans hz
        refine ⟨k, ?_⟩
        have h2d : 2 * ((3 ^ f - 1) / 2) = 3 ^ f - 1 := Nat.mul_div_cancel' h2d1
        rw [hk] at h2d
        omega
      rw [Nat.dvd_iff_mod_eq_zero] at h8
      omega
    · have h8 : 8 ∣ 3 ^ f + 1 := by
        obtain ⟨k, hk⟩ := h4z.trans hz
        refine ⟨k, ?_⟩
        have h2d : 2 * ((3 ^ f + 1) / 2) = 3 ^ f + 1 := Nat.mul_div_cancel' h2d2
        rw [hk] at h2d
        omega
      rw [Nat.dvd_iff_mod_eq_zero] at h8
      omega
  ·
    obtain ⟨z, hzdiv, hzcard, ⟨e⟩⟩ := h3
    have h3z : 3 ∣ z := by
      have h : 12 ∣ 2 * z := by rw [← hzcard]; exact h12
      obtain ⟨k, hk⟩ := h
      exact ⟨2 * k, by omega⟩
    have hq3d : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    rw [hFcard] at hzdiv
    rw [hgcd] at hzdiv
    have h3d1 : ¬ 3 ∣ (3 ^ f - 1) / 2 := by
      intro hd
      have h : 3 ∣ 3 ^ f - 1 := by
        have h' := Nat.mul_div_cancel' h2d1
        rw [← h']
        exact Dvd.dvd.mul_left hd 2
      have h1 : 3 ∣ 1 := by
        have h' := Nat.dvd_sub hq3d h
        have h2 : 3 ^ f - (3 ^ f - 1) = 1 := by
          have hpos : 0 < 3 ^ f := by positivity
          omega
        rwa [h2] at h'
      omega
    have h3d2 : ¬ 3 ∣ (3 ^ f + 1) / 2 := by
      intro hd
      have h : 3 ∣ 3 ^ f + 1 := by
        have h' := Nat.mul_div_cancel' h2d2
        rw [← h']
        exact Dvd.dvd.mul_left hd 2
      have h1 : 3 ∣ 1 := by
        have h' := Nat.dvd_sub h hq3d
        have h2 : 3 ^ f + 1 - 3 ^ f = 1 := by omega
        rwa [h2] at h'
      omega
    rcases hzdiv with hz | hz
    · exact absurd (h3z.trans hz) h3d1
    · exact absurd (h3z.trans hz) h3d2
  ·
    left
    obtain ⟨e⟩ := h4'.2
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Walter.JT.card_alternatingGroup_four
  ·
    obtain ⟨h16, ⟨e⟩⟩ := h5
    rw [h2pow] at h16
    have h1 : 9 ^ f = 16 * (9 ^ f / 16) + 9 := by
      have h := Nat.div_add_mod (9 ^ f) 16
      rw [h9_16] at h
      omega
    have h2 : 9 ^ f - 1 = 16 * (9 ^ f / 16) + 8 := by omega
    rw [h2] at h16
    have h3 : 16 ∣ 8 := by
      have h4 : 16 ∣ 16 * (9 ^ f / 16) := dvd_mul_right 16 _
      have h5 := Nat.dvd_sub h16 h4
      simp at h5
    norm_num at h3
  ·
    obtain ⟨hp5, ⟨e⟩⟩ := h6
    rcases hp5 with hp5 | hp5
    · norm_num at hp5
    · rw [h2pow] at hp5
      have h1 : 9 ^ f = 5 * (9 ^ f / 5) + 4 := by
        have h := Nat.div_add_mod (9 ^ f) 5
        rw [h9_5] at h
        omega
      have h2 : 9 ^ f - 1 = 5 * (9 ^ f / 5) + 3 := by omega
      rw [h2] at hp5
      have h3 : 5 ∣ 3 := by
        have h4 : 5 ∣ 5 * (9 ^ f / 5) := dvd_mul_right 5 _
        have h5 := Nat.dvd_sub hp5 h4
        simp at h5
      norm_num at h3
  ·
    obtain ⟨m, t, ht1, ht2, N, C, hNnorm, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ := h7
    rw [hgcd] at ht2
    have hq4 : 3 ^ f % 4 = 3 := by
      obtain ⟨i, rfl⟩ := hf
      have h : 3 ^ (2 * i + 1) = 9 ^ i * 3 := by rw [pow_succ, pow_mul]; norm_num
      have h9 : 9 ^ i % 4 = 1 := by rw [Nat.pow_mod]; norm_num
      rw [h, Nat.mul_mod, h9]
    have hhalf : (3 ^ f - 1) / 2 % 2 = 1 := by
      set v := 3 ^ f / 4 with hv
      have h1 : 3 ^ f = 4 * v + 3 := by
        have h := Nat.div_add_mod (3 ^ f) 4
        rw [hq4] at h
        omega
      have h2 : 3 ^ f - 1 = 2 * (2 * v + 1) := by omega
      rw [h2, mul_comm 2 (2 * v + 1), Nat.mul_div_cancel _ (by norm_num)]
      omega
    have htodd : Odd t := by
      rcases Nat.even_or_odd t with he | ho
      · exfalso
        obtain ⟨k, hk⟩ := he
        obtain ⟨j, hj⟩ := ht2
        have h2e : (3 ^ f - 1) / 2 = 2 * (k * j) := by rw [hj, hk]; ring
        have h2d : 2 ∣ (3 ^ f - 1) / 2 := ⟨k * j, h2e⟩
        rw [Nat.dvd_iff_mod_eq_zero] at h2d
        omega
      · exact ho
    have hcompl : Subgroup.IsComplement' N C := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      rw [← @Subgroup.normal_mul (↥R) _ N C hNnorm, hsup]
      rfl
    have hcardR : Nat.card R = 3 ^ m * t := by
      rw [← hcompl.card_mul_card, hNcard, hCcard]
    have hoddR : Nat.card R % 2 = 1 := by
      have h1 : 3 ^ m % 2 = 1 := by rw [Nat.pow_mod]; norm_num
      have h2t : t % 2 = 1 := Nat.odd_iff.mp htodd
      rw [hcardR, Nat.mul_mod, h1, h2t]
    rw [Nat.dvd_iff_mod_eq_zero] at h2
    omega
  ·
    obtain ⟨m, hm0, hmf, ⟨e⟩⟩ := h8
    have hmodd : Odd m := by
      rcases Nat.even_or_odd m with he | ho
      · exfalso
        obtain ⟨k, hk⟩ := he
        obtain ⟨j, hj⟩ := hmf
        have h2f : 2 ∣ f := ⟨k * j, by rw [hj, hk]; ring⟩
        obtain ⟨i, hi⟩ := hf
        rw [hi] at h2f
        omega
      · exact ho
    rcases Nat.lt_or_ge m 3 with hm3' | hm3'
    · left
      interval_cases m
      · exact absurd rfl hm0
      · rw [Nat.card_congr e.toEquiv]
        have hc : Nat.card (GaloisField 3 1) = 3 := by
          rw [GaloisField.card 3 1 (by norm_num)]
          norm_num
        have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 1)) := by
          rw [hc]
          exact ⟨3, 1, Nat.prime_three, ⟨1, rfl⟩, by norm_num, by norm_num⟩
        have h := CFSG.Walter.Suzuki.card_psl2_of_card (K := GaloisField 3 1) (q := 3) hK hc
        norm_num at h
        exact h
      · norm_num at hmodd
    · right
      exact ⟨m, hm3', hmf, ⟨e⟩⟩
  ·
    obtain ⟨m, hm0, h2mf, _⟩ := h9
    obtain ⟨j, hj⟩ := h2mf
    have h2f : 2 ∣ f := ⟨m * j, by rw [hj]; ring⟩
    obtain ⟨i, hi⟩ := hf
    rw [hi] at h2f
    obtain ⟨c, hc⟩ := h2f
    omega

theorem exists_reeTypeHyp_of_jtHyp
    {G : Type} [Group G] [Finite G] (h : CFSG.Walter.JT.JTHyp G) (hp3 : h.p = 3) :
    ∃ W : CFSG.Walter.Ward.ReeTypeHyp G, W.p = h.p ∧ W.f = h.f ∧ W.J = h.t ∧ W.L = h.F := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have hL := CFSG.Walter.JT.lemma_2_1 h hp
  have hward : CFSG.Walter.Ward.wardSign (h.p ^ h.f) = -1 := by
    rw [CFSG.Walter.Ward.wardSign, ← CFSG.Walter.JT.JTHyp.q_eq]
    simp [hq8]
  have hcast : ((h.p : ℤ) ^ h.f) = ((h.q : ℕ) : ℤ) := by
    rw [CFSG.Walter.JT.JTHyp.q_eq]; push_cast; ring
  refine ⟨{
    p := h.p
    f := h.f
    p_ne_two := hp
    f_pos := Nat.pos_of_ne_zero fun hf0 => by
      have := h.five_lt
      rw [hf0, pow_zero] at this
      omega
    card_sylow := fun P => (hL.2.1 P).2
    elementary_sylow := fun P => (hL.2.1 P).1
    index_ne_two := fun N _ => h.index_ne_two N
    J := h.t
    orderOf_J := h.orderOf_t
    L := h.F
    le_centralizer := h.le_centralizer
    J_not_mem := h.t_not_mem
    centralizer_eq := h.centralizer_eq
    iso := h.iso
    normalizer_le := ?_
    not_commute := ?_ }, rfl, rfl, rfl, rfl⟩
  · intro R hRF hR R₀ hR₀ hR₀1
    rw [hward, hcast] at hR
    have hR' : 2 * orderOf R + 1 = h.q := by omega
    exact h.normalizer_le_of_lemma716 hp3 (h.lemma_7_16 hp3) hRF hR' hR₀ hR₀1
  · intro J' hJ'F hJ' S hSF hS hSJ A hA hAN
    rw [hward, hcast] at hS
    have hS' : 4 * orderOf S = h.q + 1 := by omega
    exact h.not_commute_of_lemma712a hp3 (h.lemma_7_12_a hp3) hJ'F hJ' hSF hS' hSJ hA hAN

theorem jtHyp_card_eq_of_three
    {G : Type} [Group G] [Finite G] (h : CFSG.Walter.JT.JTHyp G) (hp3 : h.p = 3) :
    Nat.card G = h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1) := by
  obtain ⟨W, hWp, hWf, -, -⟩ := exists_reeTypeHyp_of_jtHyp h hp3
  have horder := (CFSG.Walter.Ward.ward_order W).2
  have hq : W.q = h.q := by
    rw [CFSG.Walter.Ward.ReeTypeHyp.q, CFSG.Walter.JT.JTHyp.q, hWp, hWf]
  rwa [hq] at horder

theorem exists_jtHyp_subgroup {G : Type} [Group G] [Finite G] (J : CFSG.Walter.JT.JTHyp G)
    (M : Subgroup G) (htM : J.t ∈ M) (hidx : ∀ N : Subgroup ↥M, N.index ≠ 2) {m : ℕ}
    (hm : 5 < J.p ^ m) (e : ↥(M.subgroupOf J.F) ≃* PSL(2, GaloisField J.p m)) :
    ∃ JM : CFSG.Walter.JT.JTHyp ↥M, JM.p = J.p ∧ JM.f = m ∧ (JM.t : G) = J.t := by
  let ee : ↥(J.F.subgroupOf M) ≃* ↥(M.subgroupOf J.F) :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_mul' := fun x y => rfl }
  refine ⟨{
    p := J.p
    f := m
    five_lt := hm
    abelian_sylow := CFSG.Walter.HasAbelianSylowTwo.subgroup J.abelian_sylow M
    index_ne_two := hidx
    t := ⟨J.t, htM⟩
    orderOf_t := by rw [Subgroup.orderOf_mk, J.orderOf_t]
    F := J.F.subgroupOf M
    le_centralizer := ?_
    t_not_mem := ?_
    centralizer_eq := ?_
    iso := ee.trans e }, rfl, rfl, rfl⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (J.commute_of_mem_F hx)
  · intro h
    exact J.t_not_mem h
  · apply le_antisymm
    · intro x hx
      have hxG : (x : G) ∈ Subgroup.centralizer ({J.t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)
      rcases J.mem_centralizer_t.mp hxG with hxF | hxF
      · exact Subgroup.mem_sup_right (show x ∈ J.F.subgroupOf M from hxF)
      · have hb : (⟨J.t * (x : G), M.mul_mem htM x.2⟩ : ↥M) ∈ J.F.subgroupOf M := hxF
        have h := Subgroup.mul_mem_sup (Subgroup.mem_zpowers (⟨J.t, htM⟩ : ↥M)) hb
        rwa [show (⟨J.t, htM⟩ : ↥M) * ⟨J.t * (x : G), M.mul_mem htM x.2⟩ = x from Subtype.ext (by
          show J.t * (J.t * (x : G)) = (x : G)
          rw [← mul_assoc, J.t_mul_t, one_mul])] at h
    · apply sup_le
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (J.commute_of_mem_F hx)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
