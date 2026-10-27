module

public import CFSG.RankThree.GF2n.Smith81.SubConfigArith
public import CFSG.Open.Defs
import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.GF2n.Smith81.SubCfg

open CFSG.Open CFSG.Timmesfeld

theorem exists_dvd_of_ppd_dvd_prod_GL {r e g n : ℕ} (hr : IsPrimitivePrimeDivisor r e)
    (he : 0 < e) (h : r ∣ ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ))) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ e ∣ g * j := by
  by_contra hcon
  exact not_dvd_prod_GL hr he (fun j hj1 hjn hd => hcon ⟨j, hj1, hjn, hd⟩) h

theorem ppd_dvd_prod_GL_of {r e g n j : ℕ} (hr : IsPrimitivePrimeDivisor r e) (he : 0 < e)
    (hj1 : 1 ≤ j) (hjn : j ≤ n) (hdvd : e ∣ g * j) :
    r ∣ ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ)) := by
  have h : r ∣ (2 ^ g) ^ n - (2 ^ g) ^ (n - j) := by
    rw [pow_sub_pow_eq (Nat.sub_le n j), Nat.sub_sub_self hjn, ← pow_mul 2 g j]
    exact dvd_mul_of_dvd_right ((hr.dvd_sub_one_iff he _).mpr hdvd) _
  exact h.trans (Finset.dvd_prod_of_mem (fun i : Fin n => (2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ))
    (Finset.mem_univ ⟨n - j, by omega⟩))

theorem prod_GL_two_part {g n : ℕ} (hg : 1 ≤ g) :
    ∃ s, Odd s ∧
      ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ)) = 2 ^ (g * (n * (n - 1) / 2)) * s := by
  have h : ∀ i : Fin n, (2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ) =
      (2 ^ g) ^ (i : ℕ) * ((2 ^ g) ^ (n - (i : ℕ)) - 1) := fun i =>
    pow_sub_pow_eq (Nat.le_of_lt i.2)
  refine ⟨∏ i : Fin n, ((2 ^ g) ^ (n - (i : ℕ)) - 1), Finset.prod_induction _ Odd
    (fun _ _ => Odd.mul) odd_one fun i _ => Orders.odd_pow_sub_one hg (by have := i.2; omega), ?_⟩
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, ← pow_mul]

theorem two_part_eq_of_ordD_eq_ordD {f g m m' : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) (hm : 1 ≤ m)
    (hm' : 1 ≤ m') (h : ordD m (2 ^ f) = ordD m' (2 ^ g)) :
    f * (m * (m - 1)) = g * (m' * (m' - 1)) := by
  obtain ⟨r, hr, hr'⟩ := (Orders.profile_ordD hm hf).two
  obtain ⟨s, hs, hs'⟩ := (Orders.profile_ordD hm' hg).two
  exact Orders.eq_of_two_pow_mul_odd hr hs (hr'.symm.trans (h.trans hs'))

theorem two_part_eq_of_ordD_eq_ordTwistedD {f g m m' : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (h : ordD m (2 ^ f) = ordTwistedD m' (2 ^ g)) :
    f * (m * (m - 1)) = g * (m' * (m' - 1)) := by
  obtain ⟨r, hr, hr'⟩ := (Orders.profile_ordD hm hf).two
  obtain ⟨s, hs, hs'⟩ := (Orders.profile_ordTwistedD hm' hg).two
  exact Orders.eq_of_two_pow_mul_odd hr hs (hr'.symm.trans (h.trans hs'))

theorem le_of_ordD_dvd_SL2 {f g m : ℕ} (hf : 1 ≤ f) (hm : 1 ≤ m) (hg : 1 ≤ g)
    (h : ordD m (2 ^ f) ∣ 2 ^ g * ((2 ^ g) ^ 2 - 1)) : f * (m * (m - 1)) ≤ g := by
  obtain ⟨r, -, hr⟩ := (Orders.profile_ordD hm hf).two
  have h2 : 2 ^ (f * (m * (m - 1))) ∣ ordD m (2 ^ f) := ⟨r, hr⟩
  have hcop : Nat.Coprime (2 ^ (f * (m * (m - 1)))) ((2 ^ g) ^ 2 - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Orders.odd_pow_sub_one hg two_pos))
  exact (Nat.pow_dvd_pow_iff_le_right one_lt_two).mp (hcop.dvd_of_dvd_mul_right (h2.trans h))

private theorem ppd_dvd_ordD_of {r k f m i : ℕ} (hr : IsPrimitivePrimeDivisor r k) (hk : 0 < k)
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hi1 : 1 ≤ i) (him : i ≤ m - 1) (hki : k ∣ f * (2 * i)) :
    r ∣ ordD m (2 ^ f) := by
  rw [ordD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (Orders.odd_pow_sub_one hf hm)),
    Nat.div_one]
  exact dvd_mul_of_dvd_right (((Orders.PrimDiv.dvd_pow_sub_one_iff hr hk f _).mpr hki).trans
    (Finset.dvd_prod_of_mem (fun l => (2 ^ f) ^ (2 * l) - 1) (Finset.mem_Icc.mpr ⟨hi1, him⟩))) _

private theorem two_part_of_ordD_mul_eq {f g m n : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) (hm : 1 ≤ m)
    (hP : ordD m (2 ^ f) * (2 ^ g - 1) = ∏ l : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (l : ℕ))) :
    f * (m * (m - 1)) = g * (n * (n - 1) / 2) := by
  obtain ⟨r, hr, hN⟩ := (Orders.profile_ordD hm hf).two
  obtain ⟨s, hs, hS⟩ := prod_GL_two_part (n := n) hg
  refine Orders.eq_of_two_pow_mul_odd (hr.mul (Orders.odd_two_pow_sub_one hg)) hs ?_
  rw [← mul_assoc, ← hN, hP, hS]

private theorem exists_dvd_of_ordD_mul_eq {f g m n i : ℕ} (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hi1 : 1 ≤ i) (him : i ≤ m - 1) (h6 : f * (2 * i) ≠ 6)
    (hP : ordD m (2 ^ f) * (2 ^ g - 1) = ∏ l : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (l : ℕ))) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ f * (2 * i) ∣ g * j := by
  have h2 : 1 * (2 * 1) ≤ f * (2 * i) := Nat.mul_le_mul hf (Nat.mul_le_mul_left 2 hi1)
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (by omega : 2 ≤ f * (2 * i)) h6
  refine exists_dvd_of_ppd_dvd_prod_GL hr (by omega) ?_
  rw [← hP]
  exact dvd_mul_of_dvd_left (ppd_dvd_ordD_of hr (by omega) hf hm hi1 him dvd_rfl) _

private theorem le_of_ordD_mul_eq {f g m n : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h6 : g * n ≠ 6)
    (hP : ordD m (2 ^ f) * (2 ^ g - 1) = ∏ l : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (l : ℕ))) :
    g * n ≤ f * (2 * (m - 1)) := by
  have hgn : g * 2 ≤ g * n := Nat.mul_le_mul_left g hn
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (by omega : 2 ≤ g * n) h6
  have hrP := ppd_dvd_prod_GL_of (g := g) (n := n) hr (by omega) (by omega) le_rfl dvd_rfl
  rw [← hP] at hrP
  rcases hr.prime.dvd_mul.mp hrP with h | h
  · exact Orders.zD_le (by omega) hm
      (((Orders.profile_ordD (n := m) (by omega) hf).prim r _ hr (by omega)).mp h)
  · have := Nat.le_of_dvd (by omega) ((hr.dvd_sub_one_iff (by omega) g).mp h)
    omega

theorem e4_ordD_mul_ne_prod_GL {f g n : ℕ} (hf : 2 ≤ f) (hg : 1 ≤ g) :
    ordD 4 (2 ^ f) * (2 ^ g - 1) ≠ ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ)) := by
  intro hP
  have h2 : f * 12 = g * (n * (n - 1) / 2) :=
    two_part_of_ordD_mul_eq (m := 4) (by omega) hg (by norm_num) hP
  have hn : 2 ≤ n := by
    by_contra hn
    have h0 : n * (n - 1) = 0 := by
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> rfl
    rw [h0, Nat.zero_div, mul_zero] at h2
    omega
  obtain ⟨j₁, hj₁1, hj₁n, hj₁⟩ := exists_dvd_of_ordD_mul_eq (m := 4) (i := 3) (by omega)
    (by norm_num) (by norm_num) (by norm_num) (by omega) hP
  have hlow : f * (2 * 3) ≤ g * n :=
    (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hj₁).trans (Nat.mul_le_mul_left g hj₁n)
  have hup : g * n ≤ f * 6 :=
    le_of_ordD_mul_eq (m := 4) (by omega) hg (by norm_num) hn (by omega) hP
  have hgn : g * n = 6 * f := by omega
  have hT : n * (n - 1) / 2 = 2 * n := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < g by omega) ?_
    calc g * (n * (n - 1) / 2) = f * 12 := h2.symm
      _ = 2 * (g * n) := by omega
      _ = g * (2 * n) := by ring
  have hn5 : n = 5 := by
    have h6 : n < 6 := by
      by_contra h6
      have : n * 5 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
      omega
    interval_cases n <;> omega
  subst hn5
  obtain ⟨j, hj1, hjn, c, hc⟩ := exists_dvd_of_ordD_mul_eq (m := 4) (i := 2) (by omega)
    (by norm_num) (by norm_num) (by norm_num) (by omega) hP
  have h20 : f * (6 * j) = f * (20 * c) := by
    calc f * (6 * j) = g * 5 * j := by rw [hgn]; ring
      _ = 5 * (g * j) := by ring
      _ = f * (20 * c) := by rw [hc]; ring
  have := Nat.eq_of_mul_eq_mul_left (show 0 < f by omega) h20
  omega

theorem e5_ordD_mul_ne_prod_GL {f g n : ℕ} (hf : 2 ≤ f) (hg : 1 ≤ g) :
    ordD 6 (2 ^ f) * (2 ^ g - 1) ≠ ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ)) := by
  intro hP
  have h2 : f * 30 = g * (n * (n - 1) / 2) :=
    two_part_of_ordD_mul_eq (m := 6) (by omega) hg (by norm_num) hP
  have hn : 2 ≤ n := by
    by_contra hn
    have h0 : n * (n - 1) = 0 := by
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> rfl
    rw [h0, Nat.zero_div, mul_zero] at h2
    omega
  obtain ⟨j₁, hj₁1, hj₁n, hj₁⟩ := exists_dvd_of_ordD_mul_eq (m := 6) (i := 5) (by omega)
    (by norm_num) (by norm_num) (by norm_num) (by omega) hP
  have hlow : f * (2 * 5) ≤ g * n :=
    (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hj₁).trans (Nat.mul_le_mul_left g hj₁n)
  have hup : g * n ≤ f * 10 :=
    le_of_ordD_mul_eq (m := 6) (by omega) hg (by norm_num) hn (by omega) hP
  have hgn : g * n = 10 * f := by omega
  have hT : n * (n - 1) / 2 = 3 * n := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < g by omega) ?_
    calc g * (n * (n - 1) / 2) = f * 30 := h2.symm
      _ = 3 * (g * n) := by omega
      _ = g * (3 * n) := by ring
  have hn7 : n = 7 := by
    have h8 : n < 8 := by
      by_contra h8
      have : n * 7 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
      omega
    interval_cases n <;> omega
  subst hn7
  obtain ⟨j, hj1, hjn, c, hc⟩ := exists_dvd_of_ordD_mul_eq (m := 6) (i := 4) (by omega)
    (by norm_num) (by norm_num) (by norm_num) (by omega) hP
  have h56 : f * (10 * j) = f * (56 * c) := by
    calc f * (10 * j) = g * 7 * j := by rw [hgn]; ring
      _ = 7 * (g * j) := by ring
      _ = f * (56 * c) := by rw [hc]; ring
  have := Nat.eq_of_mul_eq_mul_left (show 0 < f by omega) h56
  omega

end CFSG.RankThree.GF2n.Smith81.SubCfg
