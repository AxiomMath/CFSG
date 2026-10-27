module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcLang

public section

namespace CFSG.HardMathSupport.C14Exc

private lemma three_part_nine_dvd_pow_six_sub_one {q : ℕ} (hq : ¬ 3 ∣ q) : 9 ∣ q ^ 6 - 1 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero 3)
  have hcop : q.Coprime 9 := by
    simpa using Nat.Prime.coprime_pow_of_not_dvd (p := 3) (m := 2) Nat.prime_three hq
  have hmod : q ^ 6 ≡ 1 [MOD 9] := by
    have h := Nat.ModEq.pow_totient hcop
    have hphi : (9 : ℕ).totient = 6 := by
      have := Nat.totient_prime_pow Nat.prime_three (n := 2) (by norm_num)
      norm_num at this ⊢
      exact this
    simpa [hphi] using h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0))).1 hmod.symm

theorem two_le_of_not_three_pow_succ_dvd {q₀ s : ℕ} (hq₀ : ¬ 3 ∣ q₀)
    (hs : ¬ 3 ^ (s + 1) ∣ q₀ ^ 6 - 1) : 2 ≤ s := by
  have h9 := three_part_nine_dvd_pow_six_sub_one hq₀
  by_contra h
  have hpow : 3 ^ (s + 1) ∣ 3 ^ 2 := Nat.pow_dvd_pow 3 (by omega)
  exact hs (hpow.trans (by simpa using h9))


private lemma exists_three_mul_four_pow_add_sq_add_one {q : ℕ} (hq : ¬ 3 ∣ q) :
    ∃ a : ℕ, q ^ 4 + q ^ 2 + 1 = 3 * a ∧ ¬ 3 ∣ a := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero 3)
  have hcop3 : q.Coprime 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hq).symm
  have hq2mod : q ^ 2 ≡ 1 [MOD 3] := by
    simpa using Nat.ModEq.pow_card_sub_one_eq_one Nat.prime_three hcop3
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hq2).1 hq2mod.symm
  have hq2eq : q ^ 2 = 3 * k + 1 := by omega
  have hAeq : q ^ 4 + q ^ 2 + 1 = 9 * (k ^ 2 + k) + 3 := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq2eq]
    ring
  refine ⟨3 * (k ^ 2 + k) + 1, ?_, ?_⟩
  · rw [hAeq]
    ring
  · intro h3a
    rw [Nat.dvd_iff_mod_eq_zero] at h3a
    have : (3 * (k ^ 2 + k) + 1) % 3 = 1 := by omega
    omega

private lemma three_pow_sub_one_exact_dvd_sq_sub_one {q s : ℕ} (hq : ¬ 3 ∣ q)
    (hs : 3 ^ s ∣ q ^ 6 - 1) (hs' : ¬ 3 ^ (s + 1) ∣ q ^ 6 - 1) :
    ∃ m : ℕ, q ^ 2 - 1 = 3 ^ (s - 1) * m ∧ ¬ 3 ^ s ∣ q ^ 2 - 1 := by
  have hs2 : 2 ≤ s := two_le_of_not_three_pow_succ_dvd hq hs'
  obtain ⟨a, ha, ha3⟩ := exists_three_mul_four_pow_add_sq_add_one hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero 3)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)
  have hq1 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)
  have hfac : (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) = q ^ 6 - 1 := by
    rw [Nat.sub_mul, one_mul, show q ^ 2 * (q ^ 4 + q ^ 2 + 1) = q ^ 6 + q ^ 4 + q ^ 2 by ring]
    omega
  have hdvd : 3 ^ s ∣ (q ^ 2 - 1) * (3 * a) := by
    rw [← ha, hfac]
    exact hs
  have hcancel : 3 ^ (s - 1) ∣ (q ^ 2 - 1) * a := by
    have hs1 : s - 1 + 1 = s := Nat.sub_add_cancel (by omega : 1 ≤ s)
    have h3s : 3 ^ s = 3 ^ (s - 1) * 3 := by
      calc 3 ^ s = 3 ^ (s - 1 + 1) := by rw [hs1]
        _ = 3 ^ (s - 1) * 3 := pow_succ _ _
    rw [h3s] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3) (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hdvd)
  have hcop : Nat.Coprime (3 ^ (s - 1)) a :=
    (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_three ha3).symm
  have hdvd1 : 3 ^ (s - 1) ∣ q ^ 2 - 1 := hcop.dvd_of_dvd_mul_right hcancel
  have hnot : ¬ 3 ^ s ∣ q ^ 2 - 1 := by
    intro h
    apply hs'
    have hmul : 3 ^ (s + 1) ∣ (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul h ⟨a, ha⟩
    rwa [hfac] at hmul
  obtain ⟨m, hm⟩ := hdvd1
  exact ⟨m, hm, hnot⟩

private lemma exists_eq_three_pow_mul_sub_one {q s : ℕ} (hq : ¬ 3 ∣ q)
    (hs : 3 ^ s ∣ q ^ 6 - 1) (hs' : ¬ 3 ^ (s + 1) ∣ q ^ 6 - 1) :
    ∃ m : ℤ, ¬ (3 : ℤ) ∣ m ∧ (q : ℤ) ^ 2 - 1 = 3 ^ (s - 1) * m := by
  have hs2 : 2 ≤ s := two_le_of_not_three_pow_succ_dvd hq hs'
  obtain ⟨m, hm, hnot⟩ := three_pow_sub_one_exact_dvd_sq_sub_one hq hs hs'
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero 3)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)
  refine ⟨(m : ℤ), ?_, ?_⟩
  · intro h3m
    apply hnot
    have h3m' : 3 ∣ m := Int.natCast_dvd_natCast.mp (by simpa using h3m)
    have : 3 ^ s ∣ 3 ^ (s - 1) * m := by
      have hs1 : s - 1 + 1 = s := Nat.sub_add_cancel (by omega : 1 ≤ s)
      have h3s : 3 ^ s = 3 ^ (s - 1) * 3 := by
        calc 3 ^ s = 3 ^ (s - 1 + 1) := by rw [hs1]
          _ = 3 ^ (s - 1) * 3 := pow_succ _ _
      rw [h3s]
      exact Nat.mul_dvd_mul_left _ h3m'
    rw [hm]
    exact this
  · have hcast : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub hq2]
      push_cast
      ring
    rw [← hcast, hm]
    push_cast
    ring

private lemma modEq_add_of_mul_modEq {c x : ℤ} {s : ℕ} (hs : 2 ≤ s)
    (hc : c * x ≡ 1 [ZMOD 3 ^ s]) (hx : (3 : ℤ) ^ (s - 1) ∣ x - 1) :
    c + x ≡ 2 [ZMOD 3 ^ s] ∧ c ≡ 1 [ZMOD 3 ^ (s - 1)] := by
  have hdiv : (3 : ℤ) ^ (s - 1) ∣ 3 ^ s := pow_dvd_pow 3 (by omega)
  have hc_n : c * x ≡ 1 [ZMOD (3 : ℤ) ^ (s - 1)] := Int.ModEq.of_dvd hdiv hc
  have hx_n : x ≡ 1 [ZMOD (3 : ℤ) ^ (s - 1)] := by
    rw [Int.modEq_iff_dvd]
    simpa [neg_sub] using (dvd_neg.mpr hx)
  have hxc : c * x ≡ c * 1 [ZMOD (3 : ℤ) ^ (s - 1)] := hx_n.mul_left c
  have h1c : (1 : ℤ) ≡ c [ZMOD (3 : ℤ) ^ (s - 1)] :=
    hc_n.symm.trans (by simpa using hxc)
  have hc1 : c ≡ 1 [ZMOD (3 : ℤ) ^ (s - 1)] := h1c.symm
  have hcd : (3 : ℤ) ^ (s - 1) ∣ c - 1 := Int.modEq_iff_dvd.mp h1c
  have hprod : (3 : ℤ) ^ (s - 1) * 3 ^ (s - 1) ∣ (c - 1) * (x - 1) :=
    mul_dvd_mul hcd hx
  have hsq : (3 : ℤ) ^ (s - 1) * 3 ^ (s - 1) = (3 : ℤ) ^ (2 * (s - 1)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsq] at hprod
  have hmain : (3 : ℤ) ^ s ∣ (c - 1) * (x - 1) :=
    (pow_dvd_pow (3 : ℤ) (by omega : s ≤ 2 * (s - 1))).trans hprod
  have hcx : (3 : ℤ) ^ s ∣ c * x - 1 := Int.modEq_iff_dvd.mp hc.symm
  have h1 : (3 : ℤ) ^ s ∣ c * x - c - x + 1 := by
    convert hmain using 1
    ring
  have h3 : (3 : ℤ) ^ s ∣ 2 - (c + x) := by
    have := dvd_sub h1 hcx
    convert this using 1 <;> ring
  exact ⟨Int.modEq_iff_dvd.mpr h3, hc1⟩

private lemma prod_range_three_iterate {Z : Type*} [CommGroup Z] (F : Z →* Z) (z : Z) :
    (∏ i ∈ Finset.range 3, (⇑F)^[i] z) = z * F z * F (F z) := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, Finset.prod_range_succ]
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Finset.prod_range_succ]
  simp [Function.iterate_succ_apply']

private lemma three_iterate_norm_mul {Z : Type*} [CommGroup Z] (F : Z →* Z) (a b : Z) :
    (a * b) * F (a * b) * F (F (a * b)) =
      (a * F a * F (F a)) * (b * F b * F (F b)) := by
  simp only [map_mul]
  ac_rfl

private lemma three_iterate_norm_pow {Z : Type*} [CommGroup Z] (F : Z →* Z) (a : Z) (n : ℕ) :
    (a ^ n) * F (a ^ n) * F (F (a ^ n)) = (a * F a * F (F a)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, three_iterate_norm_mul, ih, pow_succ]

private lemma exists_norm_eq_of_fixed_of_pow {Z : Type*} [CommGroup Z] (F : Z →* Z)
    (hfin : ∀ z : Z, (⇑F)^[3] z = z → IsOfFinOrder z)
    (hLang : ∀ y : Z, ∃ x : Z, y = x⁻¹ * (⇑F)^[3] x)
    {y : Z} (hy : F y = y) {b : ℕ} (hb : 1 ≤ b) (hyb : y ^ 3 ^ b = 1) :
    ∃ z : Z, (⇑F)^[3] z = z ∧ (∃ n : ℕ, z ^ 3 ^ n = 1) ∧
      z * F z * F (F z) = y := by
  obtain ⟨z0, hz0fix, hz0prod⟩ := norm_surjective_of_lang F 3 hLang y hy
  have hNy : z0 * F z0 * F (F z0) = y := by
    rw [← prod_range_three_iterate F z0]
    exact hz0prod
  obtain ⟨e, m', hm'not, hm'eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (IsOfFinOrder.orderOf_pos (hfin z0 hz0fix)).ne' 3 (by norm_num : 3 ≠ 1)
  let z1 : Z := z0 ^ m'
  have hz1fix : (⇑F)^[3] z1 = z1 := by
    rw [show z1 = z0 ^ m' from rfl, iterate_map_pow, hz0fix]
  have hz1_3 : ∃ n : ℕ, z1 ^ 3 ^ n = 1 := by
    refine ⟨e, ?_⟩
    rw [show z1 = z0 ^ m' from rfl, ← pow_mul, mul_comm m' (3 ^ e), ← hm'eq]
    exact pow_orderOf_eq_one z0
  have hz1norm : z1 * F z1 * F (F z1) = y ^ m' := by
    rw [show z1 = z0 ^ m' from rfl, three_iterate_norm_pow, hNy]
  obtain ⟨m'', hm''lt, hm''⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_three hm'not)
    (Nat.one_lt_pow (by omega : b ≠ 0) (by norm_num : 1 < 3))
  refine ⟨z1 ^ m'', ?_, ?_, ?_⟩
  · rw [iterate_map_pow, hz1fix]
  · obtain ⟨n, hn⟩ := hz1_3
    refine ⟨n, ?_⟩
    rw [← pow_mul, mul_comm m'' (3 ^ n), pow_mul, hn, one_pow]
  · calc z1 ^ m'' * F (z1 ^ m'') * F (F (z1 ^ m''))
        = (z1 * F z1 * F (F z1)) ^ m'' := three_iterate_norm_pow F z1 m''
      _ = (y ^ m') ^ m'' := by rw [hz1norm]
      _ = y ^ (m' * m'') := by rw [pow_mul]
      _ = y ^ ((m' * m'') % 3 ^ b) :=
          pow_eq_pow_mod (m := m' * m'') (a := y) (n := 3 ^ b) hyb
      _ = y ^ 1 := by rw [hm'']
      _ = y := pow_one y

private lemma pow_one_add_modEq_sq (a : ℤ) (j : ℕ) :
    (1 + a) ^ j ≡ 1 + (j : ℤ) * a [ZMOD a ^ 2] := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmul : (1 + a) ^ (j + 1) ≡ (1 + (j : ℤ) * a) * (1 + a) [ZMOD a ^ 2] := by
      calc (1 + a) ^ (j + 1) = (1 + a) ^ j * (1 + a) := pow_succ _ _
        _ ≡ (1 + (j : ℤ) * a) * (1 + a) [ZMOD a ^ 2] :=
            Int.ModEq.mul ih (Int.ModEq.refl (1 + a))
    have hzero : (j : ℤ) * a ^ 2 ≡ 0 [ZMOD a ^ 2] :=
      Int.modEq_zero_iff_dvd.mpr ⟨(j : ℤ), by ring⟩
    calc (1 + a) ^ (j + 1) ≡ (1 + (j : ℤ) * a) * (1 + a)
          [ZMOD a ^ 2] := hmul
      _ = 1 + ((j + 1 : ℕ) : ℤ) * a + (j : ℤ) * a ^ 2 := by push_cast; ring
      _ ≡ 1 + ((j + 1 : ℕ) : ℤ) * a + 0 [ZMOD a ^ 2] :=
          Int.ModEq.add (Int.ModEq.refl _) hzero
      _ = 1 + ((j + 1 : ℕ) : ℤ) * a := by ring

theorem pow_three_pow_eq_one_of_iterate_three_eq {Z : Type*} [CommGroup Z] (F : Z →* Z)
    {q₀ : ℕ} (hF : ∀ z, F (F z) = z ^ q₀ ^ 2) {s : ℕ} (hs : ¬ 3 ^ (s + 1) ∣ q₀ ^ 6 - 1) {z : Z}
    (hz : (⇑F)^[3] z = z) (hz3 : ∃ n : ℕ, z ^ 3 ^ n = 1) : z ^ 3 ^ s = 1 := by
  have hq0 : q₀ ≠ 0 := by
    rintro rfl
    exact hs (by simpa using dvd_zero (3 ^ (s + 1)))
  have h2 : ∀ y : Z, (⇑F)^[2] y = y ^ q₀ ^ 2 := by
    intro y
    simpa [Function.iterate_succ_apply'] using hF y
  have h6 : ∀ y : Z, (⇑F)^[6] y = y ^ q₀ ^ 6 := by
    intro y
    have h : (⇑F)^[6] y = (⇑F)^[2] ((⇑F)^[2] ((⇑F)^[2] y)) := by
      rw [show (6 : ℕ) = 2 + (2 + 2) by norm_num, Function.iterate_add_apply,
        Function.iterate_add_apply]
    rw [h, h2, h2, h2, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hfix6 : (⇑F)^[6] z = z := by
    calc (⇑F)^[6] z = (⇑F)^[3] ((⇑F)^[3] z) := by
          rw [show (6 : ℕ) = 3 + 3 by norm_num, Function.iterate_add_apply]
      _ = z := by rw [hz, hz]
  have hz6 : z ^ q₀ ^ 6 = z := by rw [← h6 z, hfix6]
  have hsub : z ^ (q₀ ^ 6 - 1) = 1 := by
    rw [pow_sub z (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)), hz6]
    simp
  have hdvd : orderOf z ∣ q₀ ^ 6 - 1 := orderOf_dvd_of_pow_eq_one hsub
  obtain ⟨n, hn⟩ := hz3
  have hdvd3 : orderOf z ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
  obtain ⟨m, hmle, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd3
  have hms : m ≤ s := by
    by_contra h
    have hle : s + 1 ≤ m := by omega
    have hpow : 3 ^ (s + 1) ∣ 3 ^ m := pow_dvd_pow 3 hle
    rw [← hmeq] at hpow
    exact hs (hpow.trans hdvd)
  have horder : orderOf z ∣ 3 ^ s := by
    rw [hmeq]
    exact pow_dvd_pow 3 hms
  exact (orderOf_dvd_iff_pow_eq_one).mp horder

theorem map_eq_zpow_of_iterate_three_eq {Z : Type*} [CommGroup Z] (F : Z →* Z) {q₀ : ℕ}
    (hF : ∀ z, F (F z) = z ^ q₀ ^ 2) {s : ℕ} (hs : ¬ 3 ^ (s + 1) ∣ q₀ ^ 6 - 1) {c : ℤ}
    (hc : c * (q₀ : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s]) {z : Z} (hz : (⇑F)^[3] z = z)
    (hz3 : ∃ n : ℕ, z ^ 3 ^ n = 1) : F z = z ^ c := by
  have hFz_fix : (⇑F)^[3] (F z) = F z := by
    rw [← Function.iterate_succ_apply F 3 z, Function.iterate_succ_apply' F 3 z, hz]
  have hFz3 : ∃ n : ℕ, (F z) ^ 3 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hz3
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hFz_pow : (F z) ^ 3 ^ s = 1 :=
    pow_three_pow_eq_one_of_iterate_three_eq F hF hs hFz_fix hFz3
  have hz_eq : z = (F z) ^ q₀ ^ 2 := by
    calc z = (⇑F)^[3] z := hz.symm
      _ = F (F (F z)) := by simp [Function.iterate_succ_apply']
      _ = (F z) ^ q₀ ^ 2 := hF (F z)
  have horder : (orderOf (F z) : ℤ) ∣ (3 : ℤ) ^ s := by
    exact_mod_cast orderOf_dvd_of_pow_eq_one hFz_pow
  have hmod : ((q₀ ^ 2 : ℕ) : ℤ) * c ≡ 1 [ZMOD (3 : ℤ) ^ s] := by
    convert hc using 1 <;> push_cast <;> ring
  have hmod' : ((q₀ ^ 2 : ℕ) : ℤ) * c ≡ 1 [ZMOD (orderOf (F z) : ℤ)] :=
    Int.ModEq.of_dvd horder hmod
  have hcw : z ^ c = F z := by
    calc z ^ c = ((F z) ^ (q₀ ^ 2) : Z) ^ c := by
          conv_lhs => rw [hz_eq]
      _ = ((F z) ^ ((q₀ ^ 2 : ℕ) : ℤ)) ^ c := by rw [← zpow_natCast]
      _ = (F z) ^ (((q₀ ^ 2 : ℕ) : ℤ) * c) := by rw [← zpow_mul]
      _ = (F z) ^ (1 : ℤ) := by
          rw [zpow_eq_zpow_iff_modEq]
          exact hmod'
      _ = F z := zpow_one _
  exact hcw.symm

private lemma three_iterate_norm_eq_cube {Z : Type*} [CommGroup Z] (F : Z →* Z) {q₀ : ℕ}
    (hF : ∀ z, F (F z) = z ^ q₀ ^ 2) {s : ℕ} (hs : ¬ 3 ^ (s + 1) ∣ q₀ ^ 6 - 1)
    {c : ℤ} (hc : c * (q₀ : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s])
    (hc2 : c + (q₀ : ℤ) ^ 2 ≡ 2 [ZMOD 3 ^ s]) {z : Z}
    (hz : (⇑F)^[3] z = z) (hz3 : ∃ n : ℕ, z ^ 3 ^ n = 1) :
    z * F z * F (F z) = z ^ 3 := by
  have hFz : F z = z ^ c := map_eq_zpow_of_iterate_three_eq F hF hs hc hz hz3
  have hzpow : z ^ 3 ^ s = 1 := pow_three_pow_eq_one_of_iterate_three_eq F hF hs hz hz3
  have hzord : (orderOf z : ℤ) ∣ (3 : ℤ) ^ s := by
    exact_mod_cast orderOf_dvd_of_pow_eq_one hzpow
  have hmod : c + (q₀ : ℤ) ^ 2 + 1 ≡ (3 : ℤ) [ZMOD (3 : ℤ) ^ s] := by
    have h := hc2.add (Int.ModEq.refl (1 : ℤ))
    convert h using 1 <;> ring
  have hmod' : c + (q₀ : ℤ) ^ 2 + 1 ≡ (3 : ℤ) [ZMOD (orderOf z : ℤ)] :=
    Int.ModEq.of_dvd hzord hmod
  calc z * F z * F (F z)
      = z * z ^ c * F (F z) := by
          conv_lhs => enter [1, 2]; rw [hFz]
    _ = z * z ^ c * z ^ (q₀ ^ 2) := by rw [hF z]
    _ = z ^ (c + (q₀ : ℤ) ^ 2 + 1) := by
        nth_rewrite 1 [← zpow_one z]
        rw [← zpow_natCast z (q₀ ^ 2), ← zpow_add, ← zpow_add]
        congr 1
        push_cast
        ring
    _ = z ^ (3 : ℤ) := (zpow_eq_zpow_iff_modEq).mpr hmod'
    _ = z ^ 3 := zpow_natCast z 3

private lemma map_eq_self_of_three_pow_eq_one {Z : Type*} [CommGroup Z] (F : Z →* Z) {q₀ : ℕ}
    (hF : ∀ z, F (F z) = z ^ q₀ ^ 2) {s : ℕ} (hs : ¬ 3 ^ (s + 1) ∣ q₀ ^ 6 - 1)
    {c : ℤ} (hc : c * (q₀ : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s])
    (hc1 : c ≡ 1 [ZMOD 3 ^ (s - 1)]) {w : Z} (hw : (⇑F)^[3] w = w)
    (hw3 : ∃ n : ℕ, w ^ 3 ^ n = 1) (hwp : w ^ 3 ^ (s - 1) = 1) : F w = w := by
  have hFw : F w = w ^ c := map_eq_zpow_of_iterate_three_eq F hF hs hc hw hw3
  have hord : (orderOf w : ℤ) ∣ (3 : ℤ) ^ (s - 1) := by
    exact_mod_cast orderOf_dvd_of_pow_eq_one hwp
  have hm : c ≡ (1 : ℤ) [ZMOD (orderOf w : ℤ)] := Int.ModEq.of_dvd hord hc1
  have hweq : w ^ c = w := by
    calc w ^ c = w ^ (1 : ℤ) := (zpow_eq_zpow_iff_modEq).mpr hm
      _ = w := zpow_one _
  rw [hFw, hweq]

theorem exists_pow_three_pow_eq_of_lang {Z : Type*} [CommGroup Z] (F : Z →* Z) {q₀ : ℕ}
    (hq₀ : ¬ 3 ∣ q₀) (hF : ∀ z, F (F z) = z ^ q₀ ^ 2)
    (hfin : ∀ z : Z, (⇑F)^[3] z = z → IsOfFinOrder z)
    (hLang : ∀ y : Z, ∃ x : Z, y = x⁻¹ * (⇑F)^[3] x)
    {s : ℕ} (hs : 3 ^ s ∣ q₀ ^ 6 - 1) (hs' : ¬ 3 ^ (s + 1) ∣ q₀ ^ 6 - 1)
    {y : Z} (hy : y ^ 3 = 1) (hFy : F y = y) :
    ∃ z : Z, (⇑F)^[3] z = z ∧ z ^ 3 ^ s = 1 ∧ z ^ 3 ^ (s - 1) = y := by
  have hs2 : 2 ≤ s := two_le_of_not_three_pow_succ_dvd hq₀ hs'
  have hcop : Nat.Coprime (q₀ ^ 2) (3 ^ s) := by
    have h3 : Nat.Coprime q₀ 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hq₀).symm
    exact h3.pow 2 s
  obtain ⟨c, hc0⟩ := Int.mod_coprime hcop
  have hc : c * (q₀ : ℤ) ^ 2 ≡ 1 [ZMOD (3 : ℤ) ^ s] := by
    have h := hc0
    rw [show ((q₀ ^ 2 : ℕ) : ℤ) = (q₀ : ℤ) ^ 2 by push_cast; ring,
      show ((3 ^ s : ℕ) : ℤ) = (3 : ℤ) ^ s by push_cast; ring] at h
    simpa [mul_comm] using h
  obtain ⟨m, hm3, hm_eq⟩ := exists_eq_three_pow_mul_sub_one hq₀ hs hs'
  obtain ⟨hc2, hc1⟩ := modEq_add_of_mul_modEq hs2 hc ⟨m, hm_eq⟩
  have hyfix : (⇑F)^[3] y = y := by
    simp [Function.iterate_succ_apply', hFy]
  have key : ∀ k : ℕ, k ≤ s - 1 → ∃ w : Z, (⇑F)^[3] w = w ∧
      w ^ 3 ^ (k + 1) = 1 ∧ w ^ 3 ^ k = y := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨y, hyfix, by simpa using hy, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hwfix, hwpow, hwy⟩ := ih (by omega : k ≤ s - 1)
      have hws : w ^ 3 ^ (s - 1) = 1 := by
        obtain ⟨t, ht⟩ := pow_dvd_pow 3 (by omega : k + 1 ≤ s - 1)
        rw [ht, pow_mul, hwpow, one_pow]
      have hFw : F w = w :=
        map_eq_self_of_three_pow_eq_one F hF hs' hc hc1 hwfix ⟨k + 1, hwpow⟩ hws
      obtain ⟨z, hzfix, hz3, hzN⟩ :=
        exists_norm_eq_of_fixed_of_pow F hfin hLang hFw (by omega : 1 ≤ k + 1) hwpow
      have hzcube : z ^ 3 = w := by
        rw [← three_iterate_norm_eq_cube F hF hs' hc hc2 hzfix hz3, hzN]
      refine ⟨z, hzfix, ?_, ?_⟩
      · rw [pow_succ' 3 (k + 1), pow_mul, hzcube, hwpow]
      · rw [pow_succ' 3 k, pow_mul, hzcube, hwy]
  obtain ⟨w, hwfix, hwpow, hwy⟩ := key (s - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hwpow
  exact ⟨w, hwfix, hwpow, hwy⟩

private lemma pow_modEq_one_add_three_pow_mul {q₀ s : ℕ} {c : ℤ}
    (hq₀ : ¬ 3 ∣ q₀) (hs : 3 ^ s ∣ q₀ ^ 6 - 1)
    (hs' : ¬ 3 ^ (s + 1) ∣ q₀ ^ 6 - 1)
    (hc : c * (q₀ : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s]) :
    ∃ t : ℤ, ¬ 3 ∣ t ∧ c ≡ 1 + 3 ^ (s - 1) * t [ZMOD (3 : ℤ) ^ s] := by
  have hs2 : 2 ≤ s := two_le_of_not_three_pow_succ_dvd hq₀ hs'
  obtain ⟨m, hm3, hm_eq⟩ := exists_eq_three_pow_mul_sub_one hq₀ hs hs'
  obtain ⟨hc2, _hc1⟩ := modEq_add_of_mul_modEq hs2 hc ⟨m, hm_eq⟩
  have hm3' : ¬ (3 : ℤ) ∣ (m : ℤ) := by
    intro h
    exact hm3 (by simpa using h)
  have hq2eq : (q₀ : ℤ) ^ 2 = 1 + 3 ^ (s - 1) * m := by linarith
  have hcmod : c ≡ 1 + 3 ^ (s - 1) * (-m) [ZMOD (3 : ℤ) ^ s] := by
    have hq2mod : (q₀ : ℤ) ^ 2 ≡ 1 + 3 ^ (s - 1) * m [ZMOD (3 : ℤ) ^ s] := by
      rw [hq2eq]
    have hsub := hc2.sub hq2mod
    convert hsub using 1 <;> ring
  refine ⟨-m, ?_, hcmod⟩
  rw [Int.dvd_neg]
  exact hm3'


private lemma pow_one_add_three_pow_mul_modEq {s : ℕ} (hs : 2 ≤ s) (t : ℤ) (j : ℕ) :
    (1 + 3 ^ (s - 1) * t) ^ j ≡
      1 + 3 ^ (s - 1) * ((j : ℤ) * t) [ZMOD (3 : ℤ) ^ s] := by
  have h3dvd : (3 : ℤ) ^ s ∣ (3 ^ (s - 1) * t) ^ 2 := by
    rw [mul_pow]
    have h1 : (3 : ℤ) ^ s ∣ ((3 : ℤ) ^ (s - 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by omega : s ≤ (s - 1) * 2)
    exact h1.trans (dvd_mul_right _ _)
  have hmain : (1 + 3 ^ (s - 1) * t) ^ j ≡
      1 + (j : ℤ) * (3 ^ (s - 1) * t) [ZMOD (3 : ℤ) ^ s] :=
    Int.ModEq.of_dvd h3dvd (pow_one_add_modEq_sq (3 ^ (s - 1) * t) j)
  convert hmain using 1 <;> ring


private lemma exists_nat_modEq_three_pow_mul {s : ℕ} (hs : 1 ≤ s) {x : ℤ}
    (hx : ¬ 3 ∣ x) :
    ∃ k : ℕ, ¬ 3 ∣ k ∧ 3 ^ (s - 1) * x ≡ 3 ^ (s - 1) * k [ZMOD (3 : ℤ) ^ s] := by
  let r : ℤ := x % 3
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by norm_num : (3 : ℤ) ≠ 0)
  have hrlt : r < 3 := Int.emod_lt_of_pos _ (by norm_num : (0 : ℤ) < 3)
  have hrne : r ≠ 0 := by
    intro h0
    exact hx (Int.dvd_of_emod_eq_zero (by simpa [r] using h0))
  have hr : r = 1 ∨ r = 2 := by omega
  let k : ℕ := r.toNat
  have hkval : (k : ℤ) = r := Int.toNat_of_nonneg hr0
  have hkmod : 3 ^ (s - 1) * (k : ℤ) ≡ 3 ^ (s - 1) * x [ZMOD (3 : ℤ) ^ s] := by
    have hr_eq : (k : ℤ) ≡ x [ZMOD (3 : ℤ)] := by
      rw [hkval]
      exact Int.mod_modEq x 3
    have hd : (3 : ℤ) ∣ x - (k : ℤ) := Int.modEq_iff_dvd.mp hr_eq
    have hscale : (3 : ℤ) ^ s ∣ 3 ^ (s - 1) * (x - (k : ℤ)) := by
      have hs1 : s - 1 + 1 = s := Nat.sub_add_cancel hs
      have h3s : (3 : ℤ) ^ s = 3 ^ (s - 1) * 3 := by
        calc (3 : ℤ) ^ s = 3 ^ (s - 1 + 1) := by rw [hs1]
          _ = 3 ^ (s - 1) * 3 := pow_succ _ _
      rw [h3s]
      exact mul_dvd_mul_left _ hd
    rw [Int.modEq_iff_dvd]
    convert hscale using 1 <;> ring
  refine ⟨k, ?_, hkmod.symm⟩
  rcases hr with h | h
  · have hk1 : k = 1 := by omega
    simp [hk1]
  · have hk2 : k = 2 := by omega
    simp [hk2]


theorem exists_pow_modEq_one_add_three_pow_mul {q₀ s : ℕ} (hq₀ : ¬ 3 ∣ q₀)
    (hs : 3 ^ s ∣ q₀ ^ 6 - 1) (hs' : ¬ 3 ^ (s + 1) ∣ q₀ ^ 6 - 1) {c : ℤ}
    (hc : c * (q₀ : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s]) {j : ℕ} (hj : ¬ 3 ∣ j) :
    ∃ k : ℕ, ¬ 3 ∣ k ∧ c ^ j ≡ 1 + 3 ^ (s - 1) * k [ZMOD 3 ^ s] := by
  obtain ⟨t, ht3, hcmod⟩ := pow_modEq_one_add_three_pow_mul hq₀ hs hs' hc
  have hs2 : 2 ≤ s := two_le_of_not_three_pow_succ_dvd hq₀ hs'
  have hmain : c ^ j ≡ 1 + 3 ^ (s - 1) * ((j : ℤ) * t) [ZMOD (3 : ℤ) ^ s] :=
    (hcmod.pow j).trans (pow_one_add_three_pow_mul_modEq hs2 t j)
  have hjt3 : ¬ (3 : ℤ) ∣ (j : ℤ) * t := by
    rintro h
    rcases Int.Prime.dvd_mul' Nat.prime_three h with h1 | h2
    · exact hj (by exact_mod_cast h1)
    · exact ht3 h2
  obtain ⟨k, hk3, hkmod⟩ :=
    exists_nat_modEq_three_pow_mul (s := s) (by omega : 1 ≤ s) (x := (j : ℤ) * t) hjt3
  refine ⟨k, hk3, ?_⟩
  exact hmain.trans (Int.ModEq.add (Int.ModEq.refl 1) hkmod)


end CFSG.HardMathSupport.C14Exc
