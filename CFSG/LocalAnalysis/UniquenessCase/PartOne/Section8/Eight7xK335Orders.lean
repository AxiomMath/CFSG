module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator
  lieOrderDivisor lieSylowExponent)

theorem k335_card_lie (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) :
    Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) :=
  (hO X t n p f h.admissible h).2.1

theorem k335_three_not_dvd {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : ¬ 3 ∣ p ^ f := fun hd =>
  hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow hd)).symm

theorem k335_ne_three {X : Type} [Group X] {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) (hq : p ^ f % 3 ≠ 0) : p ≠ 3 := by
  rintro rfl
  obtain ⟨-, hf, -⟩ := h.admissible
  exact hq (Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega)))

theorem k335_one_le_v3 {q : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) : 1 ≤ (q ^ 2 - 1).factorization 3 := by
  have h1 : q ^ 2 % 3 = 1 := by
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_three (by omega) (by omega)

private theorem k335v3_fac_eq_zero_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) : n.factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd h

private theorem k335v3_fac_two_mul {j : ℕ} (hj : j ≠ 0) :
    (2 * j).factorization 3 = j.factorization 3 := by
  rw [Nat.factorization_mul (by norm_num) hj, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 2), zero_add]

private theorem k335v3_sq_sub_one {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
  zify [hq, h1]
  ring

private theorem k335v3_three_dvd_sub {q : ℕ} (hq : 1 ≤ q) (h : q % 3 = 1) : 3 ∣ q - 1 := by
  have hme : q ≡ 1 [MOD 3] := by
    show q % 3 = 1 % 3
    rw [h, Nat.mod_eq_of_lt (by norm_num : 1 < 3)]
  exact (Nat.modEq_iff_dvd' hq).mp hme.symm

private theorem k335v3_three_dvd_add {q : ℕ} (h : q % 3 = 2) : 3 ∣ q + 1 := by
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, h]

private theorem k335v3_not_dvd_add_one {q : ℕ} (h : q % 3 = 1) : ¬ 3 ∣ q + 1 := by
  intro hd
  have h0 : (q + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  have h1 : (q + 1) % 3 = 2 := by rw [Nat.add_mod, h]
  omega

private theorem k335v3_not_dvd_sub_one {q : ℕ} (hq : 1 ≤ q) (h : q % 3 = 2) :
    ¬ 3 ∣ q - 1 := by
  intro hd
  have hq2 : q ≡ 2 [MOD 3] := by
    show q % 3 = 2 % 3
    rw [h, Nat.mod_eq_of_lt (by norm_num : 2 < 3)]
  have hsub : q - 1 ≡ 2 - 1 [MOD 3] :=
    Nat.ModEq.sub hq (by norm_num : 1 ≤ 2) hq2 (Nat.ModEq.refl 1)
  have h0 : q - 1 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr hd
  have h10 : (1 : ℕ) ≡ 0 [MOD 3] := hsub.symm.trans h0
  rw [Nat.ModEq] at h10
  norm_num at h10

private theorem k335v3_sq_modEq_one {q : ℕ} (h : q % 3 = 2) : q ^ 2 ≡ 1 [MOD 3] := by
  have hq2 : q ≡ 2 [MOD 3] := by
    show q % 3 = 2 % 3
    rw [h, Nat.mod_eq_of_lt (by norm_num : 2 < 3)]
  have h2 := hq2.pow 2
  rw [Nat.ModEq] at h2
  rw [show (2 : ℕ) ^ 2 % 3 = 1 by norm_num] at h2
  show q ^ 2 % 3 = 1 % 3
  rw [h2, Nat.mod_eq_of_lt (by norm_num : 1 < 3)]

private theorem k335v3_pow_mod_of_mod1 {q i : ℕ} (h : q % 3 = 1) : q ^ i % 3 = 1 := by
  have hq1 : q ≡ 1 [MOD 3] := by
    show q % 3 = 1 % 3
    rw [h, Nat.mod_eq_of_lt (by norm_num : 1 < 3)]
  simpa [Nat.ModEq] using hq1.pow i

private theorem k335v3_pow_mod_of_even {q i : ℕ} (h : q % 3 = 2) (hev : Even i) :
    q ^ i % 3 = 1 := by
  obtain ⟨j, hj⟩ := (even_iff_exists_two_mul).mp hev
  have hpow : q ^ i ≡ 1 [MOD 3] := by
    rw [hj, pow_mul]
    simpa using (k335v3_sq_modEq_one h).pow j
  simpa [Nat.ModEq] using hpow

private theorem k335v3_pow_mod_of_odd {q i : ℕ} (h : q % 3 = 2) (ho : Odd i) :
    q ^ i % 3 = 2 := by
  obtain ⟨j, hj⟩ := ho
  have hq2 : q ≡ 2 [MOD 3] := by
    show q % 3 = 2 % 3
    rw [h, Nat.mod_eq_of_lt (by norm_num : 2 < 3)]
  have hpow : q ^ i ≡ 2 [MOD 3] := by
    rw [hj, pow_succ, pow_mul]
    have h1 : (q ^ 2) ^ j ≡ 1 [MOD 3] := by simpa using (k335v3_sq_modEq_one h).pow j
    simpa using h1.mul hq2
  simpa [Nat.ModEq] using hpow

private theorem k335v3_lte_sub {q i : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q)
    (hdiv : 3 ∣ q - 1) (hi : i ≠ 0) :
    (q ^ i - 1).factorization 3 = (q - 1).factorization 3 + i.factorization 3 := by
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.factorization_def _ Nat.prime_three]
  have h := padicValNat.pow_sub_pow (p := 3) (x := q) (y := 1)
    (show Odd 3 from ⟨1, by norm_num⟩) (by omega : 1 < q) (by simpa using hdiv) h3 hi
  simpa using h

private theorem k335v3_lte_add {q i : ℕ} (h3 : ¬ 3 ∣ q)
    (hdiv : 3 ∣ q + 1) (hi : Odd i) :
    (q ^ i + 1).factorization 3 = (q + 1).factorization 3 + i.factorization 3 := by
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.factorization_def _ Nat.prime_three]
  have h := padicValNat.pow_add_pow (p := 3) (x := q) (y := 1)
    (show Odd 3 from ⟨1, by norm_num⟩) (by simpa using hdiv) h3 hi
  simpa using h

private theorem k335v3_lte_sub_sq {q j : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q)
    (hdiv : 3 ∣ q ^ 2 - 1) (hj : j ≠ 0) :
    ((q ^ 2) ^ j - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + j.factorization 3 := by
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.factorization_def _ Nat.prime_three]
  have h3q2 : ¬ 3 ∣ q ^ 2 := fun hd => h3 (Nat.prime_three.dvd_of_dvd_pow hd)
  have h := padicValNat.pow_sub_pow (p := 3) (x := q ^ 2) (y := 1)
    (show Odd 3 from ⟨1, by norm_num⟩) (by nlinarith : 1 < q ^ 2) (by simpa using hdiv) h3q2 hj
  simpa using h

private theorem k335v3_A_eq_sub {q : ℕ} (hq : 2 ≤ q) (hm : q % 3 = 1) :
    (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := k335v3_sq_sub_one (by omega)
  rw [hfac, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    k335v3_fac_eq_zero_of_not_dvd (k335v3_not_dvd_add_one hm), add_zero]

private theorem k335v3_A_eq_add {q : ℕ} (hq : 2 ≤ q) (hm : q % 3 = 2) :
    (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 := by
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := k335v3_sq_sub_one (by omega)
  rw [hfac, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    k335v3_fac_eq_zero_of_not_dvd (k335v3_not_dvd_sub_one (by omega) hm), zero_add]

private theorem k335v3_sub_mod1 {q i : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) (hm : q % 3 = 1)
    (hi : 1 ≤ i) :
    (q ^ i - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + i.factorization 3 := by
  rw [k335v3_lte_sub hq h3 (k335v3_three_dvd_sub (by omega) hm) (by omega),
    k335v3_A_eq_sub hq hm]

private theorem k335v3_sub_mod2_even {q i : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q)
    (hm : q % 3 = 2) (hev : Even i) (hi : 1 ≤ i) :
    (q ^ i - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + i.factorization 3 := by
  obtain ⟨j, hj⟩ := (even_iff_exists_two_mul).mp hev
  have hj0 : j ≠ 0 := by omega
  have hdiv : 3 ∣ q ^ 2 - 1 := by
    rw [k335v3_sq_sub_one (by omega)]
    exact dvd_mul_of_dvd_right (k335v3_three_dvd_add hm) (q - 1)
  have hlte := k335v3_lte_sub_sq hq h3 hdiv hj0
  have hpow : q ^ i = (q ^ 2) ^ j := by rw [hj, pow_mul]
  have hfac : i.factorization 3 = j.factorization 3 := by
    rw [hj]; exact k335v3_fac_two_mul hj0
  rw [hpow, hfac]
  exact hlte

private theorem k335v3_add_mod1_zero {q i : ℕ} (hm : q % 3 = 1) :
    (q ^ i + 1).factorization 3 = 0 :=
  k335v3_fac_eq_zero_of_not_dvd fun hd => by
    have hpow : q ^ i % 3 = 1 := k335v3_pow_mod_of_mod1 hm
    have h0 : (q ^ i + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    have h1 : (q ^ i + 1) % 3 = 2 := by rw [Nat.add_mod, hpow]
    omega

private theorem k335v3_add_mod2_even_zero {q i : ℕ} (hm : q % 3 = 2) (hev : Even i) :
    (q ^ i + 1).factorization 3 = 0 :=
  k335v3_fac_eq_zero_of_not_dvd fun hd => by
    have hpow : q ^ i % 3 = 1 := k335v3_pow_mod_of_even hm hev
    have h0 : (q ^ i + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    have h1 : (q ^ i + 1) % 3 = 2 := by rw [Nat.add_mod, hpow]
    omega

private theorem k335v3_sub_mod2_odd_zero {q i : ℕ} (hq : 1 ≤ q) (hm : q % 3 = 2)
    (ho : Odd i) : (q ^ i - 1).factorization 3 = 0 :=
  k335v3_fac_eq_zero_of_not_dvd fun hd => by
    have hmod : q ^ i ≡ 2 [MOD 3] := by
      show q ^ i % 3 = 2 % 3
      rw [k335v3_pow_mod_of_odd hm ho, Nat.mod_eq_of_lt (by norm_num : 2 < 3)]
    have hsub : q ^ i - 1 ≡ 2 - 1 [MOD 3] :=
      Nat.ModEq.sub (Nat.one_le_pow i q (by omega)) (by norm_num : 1 ≤ 2) hmod
        (Nat.ModEq.refl 1)
    have h1 : (q ^ i - 1) % 3 = 1 := by simpa [Nat.ModEq] using hsub
    have h0 : (q ^ i - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

theorem k335_v3_pow {q : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) {i : ℕ} (hi : 1 ≤ i) :
    (q ^ i - 1).factorization 3 =
        (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
      (q ^ i + 1).factorization 3 =
        (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) := by
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by
    have hlt : q % 3 < 3 := Nat.mod_lt q (by norm_num)
    have hne : q % 3 ≠ 0 := fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
    omega
  rcases hmod with hm | hm
  · refine ⟨?_, ?_⟩
    · rw [if_pos (Or.inl hm)]
      exact k335v3_sub_mod1 hq h3 hm hi
    · rw [if_neg (by rintro ⟨h2, -⟩; omega)]
      exact k335v3_add_mod1_zero hm
  · rcases Nat.even_or_odd i with hev | ho
    · refine ⟨?_, ?_⟩
      · rw [if_pos (Or.inr hev)]
        exact k335v3_sub_mod2_even hq h3 hm hev hi
      · rw [if_neg (by rintro ⟨-, ho'⟩; exact (Nat.not_even_iff_odd.mpr ho') hev)]
        exact k335v3_add_mod2_even_zero hm hev
    · refine ⟨?_, ?_⟩
      · rw [if_neg (by
          rintro (h1 | he)
          · omega
          · exact (Nat.not_even_iff_odd.mpr ho) he)]
        exact k335v3_sub_mod2_odd_zero (by omega) hm ho
      · rw [if_pos ⟨hm, ho⟩, k335v3_lte_add h3 (k335v3_three_dvd_add hm) ho,
          k335v3_A_eq_add hq hm]

private def k335vcl_PowHyp : Prop :=
  ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
    (q ^ i - 1).factorization 3 =
        (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
      (q ^ i + 1).factorization 3 =
        (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0)

private theorem k335vcl_sub_ne_zero {q i : ℕ} (hq : 2 ≤ q) (hi : 1 ≤ i) : q ^ i - 1 ≠ 0 := by
  have h1 : 2 ≤ 2 ^ i := by
    simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi
  have h2 : 2 ≤ q ^ i := le_trans h1 (Nat.pow_le_pow_left hq i)
  omega

private theorem k335vcl_pow_fact {q k : ℕ} (h3 : ¬ 3 ∣ q) : (q ^ k).factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun hd => h3 (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem k335vcl_v3_sub_even (hpow : k335vcl_PowHyp) {q i : ℕ}
    (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) (hi : 1 ≤ i) (hev : Even i) :
    (q ^ i - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + i.factorization 3 := by
  have h := (hpow hq h3 hi).1
  rw [if_pos (Or.inr hev)] at h
  exact h

private theorem k335vcl_v3_sub_odd (hpow : k335vcl_PowHyp) {q i : ℕ}
    (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) (hi : 1 ≤ i) (hm : q % 3 = 2) (ho : Odd i) :
    (q ^ i - 1).factorization 3 = 0 := by
  have h := (hpow hq h3 hi).1
  rw [if_neg] at h
  · exact h
  · rintro (h1 | h2)
    · omega
    · exact (Nat.not_even_iff_odd.mpr ho) h2

private theorem k335vcl_v3_sub_modone (hpow : k335vcl_PowHyp) {q i : ℕ}
    (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) (hi : 1 ≤ i) (hm : q % 3 = 1) :
    (q ^ i - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + i.factorization 3 := by
  have h := (hpow hq h3 hi).1
  rw [if_pos (Or.inl hm)] at h
  exact h

private theorem k335vcl_v3_add_odd (hpow : k335vcl_PowHyp) {q i : ℕ}
    (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) (hi : 1 ≤ i) (hm : q % 3 = 2) (ho : Odd i) :
    (q ^ i + 1).factorization 3 = (q ^ 2 - 1).factorization 3 + i.factorization 3 := by
  have h := (hpow hq h3 hi).2
  rw [if_pos ⟨hm, ho⟩] at h
  exact h

private theorem k335vcl_v3_add_even (hpow : k335vcl_PowHyp) {q i : ℕ}
    (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) (hi : 1 ≤ i) (hev : Even i) :
    (q ^ i + 1).factorization 3 = 0 := by
  have h := (hpow hq h3 hi).2
  rw [if_neg] at h
  · exact h
  · rintro ⟨-, ho⟩
    exact (Nat.not_even_iff_odd.mpr ho) hev

private theorem k335vcl_v3_add_modone (hpow : k335vcl_PowHyp) {q i : ℕ}
    (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) (hi : 1 ≤ i) (hm : q % 3 = 1) :
    (q ^ i + 1).factorization 3 = 0 := by
  have h := (hpow hq h3 hi).2
  rw [if_neg] at h
  · exact h
  · rintro ⟨h1, -⟩
    omega

private theorem k335vcl_fact_six : (6:ℕ).factorization 3 = 1 := by
  rw [show (6:ℕ) = 3 * 2 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 2), add_zero]

private theorem k335vcl_divisor_ne_zero {q : ℕ} (hq : 2 ≤ q) (t : CFSG.Open.StatedLieTag)
    (n : ℕ) : lieOrderDivisor t n q ≠ 0 := by
  have h1 : 0 < q - 1 := by omega
  have h2 : 0 < q + 1 := by omega
  cases t <;> simp only [lieOrderDivisor] <;> positivity

private theorem k335vcl_not_dvd_sub_one {q : ℕ} (h : q % 3 = 2) : ¬ 3 ∣ q - 1 := by
  intro hd
  have h0 : (q - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

private theorem k335vcl_not_dvd_add_one {q : ℕ} (h : q % 3 = 1) : ¬ 3 ∣ q + 1 := by
  intro hd
  have h0 : (q + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

private theorem k335vcl_num_psp (hpow : k335vcl_PowHyp) {q : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) :
    (lieOrderNumerator .PSp 3 q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  have hv4 := k335vcl_v3_sub_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  have hv6 := k335vcl_v3_sub_even hpow hq h3 (i := 6) (by norm_num) (by norm_num)
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 4), add_zero] at hv4
  rw [k335vcl_fact_six] at hv6
  have hnum : lieOrderNumerator .PSp 3 q = q^9 * ((q^2-1)*(q^4-1)*(q^6-1)) := by
    simp only [lieOrderNumerator]
    rw [Finset.prod_Icc_succ_top (show 1 ≤ 2 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 1 ≤ 1 + 1 by norm_num)]
    rw [Finset.Icc_self, Finset.prod_singleton]
    norm_num
  rw [hnum]
  have h2nz := k335vcl_sub_ne_zero hq (show 1 ≤ (2:ℕ) by norm_num)
  have h4nz := k335vcl_sub_ne_zero hq (show 1 ≤ (4:ℕ) by norm_num)
  have h6nz := k335vcl_sub_ne_zero hq (show 1 ≤ (6:ℕ) by norm_num)
  have hq9nz : q ^ 9 ≠ 0 := pow_ne_zero 9 (by omega)
  rw [Nat.factorization_mul hq9nz (mul_ne_zero (mul_ne_zero h2nz h4nz) h6nz),
    Nat.factorization_mul (mul_ne_zero h2nz h4nz) h6nz,
    Nat.factorization_mul h2nz h4nz]
  simp only [Finsupp.add_apply, k335vcl_pow_fact h3, hv4, hv6]
  ring

private theorem k335vcl_num_pominus (hpow : k335vcl_PowHyp) {q : ℕ} (hq : 2 ≤ q)
    (h3 : ¬ 3 ∣ q) :
    (lieOrderNumerator .POmegaMinus 4 q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  have hv4 := k335vcl_v3_sub_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  have hv6 := k335vcl_v3_sub_even hpow hq h3 (i := 6) (by norm_num) (by norm_num)
  have hv4a := k335vcl_v3_add_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 4), add_zero] at hv4
  rw [k335vcl_fact_six] at hv6
  have hnum : lieOrderNumerator .POmegaMinus 4 q
      = q^12 * (q^4+1) * ((q^2-1)*(q^4-1)*(q^6-1)) := by
    simp only [lieOrderNumerator]
    rw [Finset.prod_Icc_succ_top (show 1 ≤ 2 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 1 ≤ 1 + 1 by norm_num)]
    rw [Finset.Icc_self, Finset.prod_singleton]
  rw [hnum]
  have h12nz : q ^ 12 ≠ 0 := pow_ne_zero 12 (by omega)
  have h4p1nz : q^4+1 ≠ 0 := by positivity
  have h2nz := k335vcl_sub_ne_zero hq (show 1 ≤ (2:ℕ) by norm_num)
  have h4nz := k335vcl_sub_ne_zero hq (show 1 ≤ (4:ℕ) by norm_num)
  have h6nz := k335vcl_sub_ne_zero hq (show 1 ≤ (6:ℕ) by norm_num)
  have h23nz : (q^2-1)*(q^4-1) ≠ 0 := mul_ne_zero h2nz h4nz
  have hPnz : (q^2-1)*(q^4-1)*(q^6-1) ≠ 0 := mul_ne_zero h23nz h6nz
  rw [Nat.factorization_mul (mul_ne_zero h12nz h4p1nz) hPnz,
    Nat.factorization_mul h12nz h4p1nz,
    Nat.factorization_mul h23nz h6nz,
    Nat.factorization_mul h2nz h4nz]
  simp only [Finsupp.add_apply, k335vcl_pow_fact h3, hv4, hv6, hv4a]
  ring

private theorem k335vcl_num_psl4 (hpow : k335vcl_PowHyp) {q : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q)
    (hm : q % 3 = 1) :
    (lieOrderNumerator .PSL 4 q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  have hv3 := k335vcl_v3_sub_modone hpow hq h3 (i := 3) (by norm_num) hm
  have hv4 := k335vcl_v3_sub_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  rw [Nat.Prime.factorization_self Nat.prime_three] at hv3
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 4), add_zero] at hv4
  have hnum : lieOrderNumerator .PSL 4 q = q^6 * ((q^2-1)*(q^3-1)*(q^4-1)) := by
    simp only [lieOrderNumerator]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 3 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num)]
    rw [Finset.Icc_self, Finset.prod_singleton]
  rw [hnum]
  have h6nz : q ^ 6 ≠ 0 := pow_ne_zero 6 (by omega)
  have h2nz := k335vcl_sub_ne_zero hq (show 1 ≤ (2:ℕ) by norm_num)
  have h3nz := k335vcl_sub_ne_zero hq (show 1 ≤ (3:ℕ) by norm_num)
  have h4nz := k335vcl_sub_ne_zero hq (show 1 ≤ (4:ℕ) by norm_num)
  have h23nz : (q^2-1)*(q^3-1) ≠ 0 := mul_ne_zero h2nz h3nz
  have hPnz : (q^2-1)*(q^3-1)*(q^4-1) ≠ 0 := mul_ne_zero h23nz h4nz
  rw [Nat.factorization_mul h6nz hPnz, Nat.factorization_mul h23nz h4nz,
    Nat.factorization_mul h2nz h3nz]
  simp only [Finsupp.add_apply, k335vcl_pow_fact h3, hv3, hv4]
  ring

private theorem k335vcl_num_psu4 (hpow : k335vcl_PowHyp) {q : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q)
    (hm : q % 3 = 2) :
    (lieOrderNumerator .PSU 4 q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  have hv3 := k335vcl_v3_add_odd hpow hq h3 (i := 3) (by norm_num) hm (by norm_num)
  have hv4 := k335vcl_v3_sub_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  rw [Nat.Prime.factorization_self Nat.prime_three] at hv3
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 4), add_zero] at hv4
  have hnum : lieOrderNumerator .PSU 4 q = q^6 * ((q^2-1)*(q^3+1)*(q^4-1)) := by
    simp only [lieOrderNumerator]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 3 + 1 by norm_num)]
    rw [if_pos (show Even (4:ℕ) by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num)]
    rw [if_neg (show ¬ Even (3:ℕ) by norm_num)]
    rw [Finset.Icc_self, Finset.prod_singleton]
    rw [if_pos (show Even (2:ℕ) by norm_num)]
  rw [hnum]
  have h6nz : q ^ 6 ≠ 0 := pow_ne_zero 6 (by omega)
  have h2nz := k335vcl_sub_ne_zero hq (show 1 ≤ (2:ℕ) by norm_num)
  have h3nz : q^3+1 ≠ 0 := by positivity
  have h4nz := k335vcl_sub_ne_zero hq (show 1 ≤ (4:ℕ) by norm_num)
  have h23nz : (q^2-1)*(q^3+1) ≠ 0 := mul_ne_zero h2nz h3nz
  have hPnz : (q^2-1)*(q^3+1)*(q^4-1) ≠ 0 := mul_ne_zero h23nz h4nz
  rw [Nat.factorization_mul h6nz hPnz, Nat.factorization_mul h23nz h4nz,
    Nat.factorization_mul h2nz h3nz]
  simp only [Finsupp.add_apply, k335vcl_pow_fact h3, hv3, hv4]
  ring

private theorem k335vcl_num_psl6 (hpow : k335vcl_PowHyp) {q : ℕ} (hq : 2 ≤ q)
    (h3 : ¬ 3 ∣ q) (hm : q % 3 = 2) :
    (lieOrderNumerator .PSL 6 q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  have hv3 := k335vcl_v3_sub_odd hpow hq h3 (i := 3) (by norm_num) hm (by norm_num)
  have hv4 := k335vcl_v3_sub_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  have hv5 := k335vcl_v3_sub_odd hpow hq h3 (i := 5) (by norm_num) hm (by norm_num)
  have hv6 := k335vcl_v3_sub_even hpow hq h3 (i := 6) (by norm_num) (by norm_num)
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 4), add_zero] at hv4
  rw [k335vcl_fact_six] at hv6
  have hnum : lieOrderNumerator .PSL 6 q
      = q^15 * ((q^2-1)*(q^3-1)*(q^4-1)*(q^5-1)*(q^6-1)) := by
    simp only [lieOrderNumerator]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 5 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 4 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 3 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num)]
    rw [Finset.Icc_self, Finset.prod_singleton]
  rw [hnum]
  have h15nz : q ^ 15 ≠ 0 := pow_ne_zero 15 (by omega)
  have h2nz := k335vcl_sub_ne_zero hq (show 1 ≤ (2:ℕ) by norm_num)
  have h3nz := k335vcl_sub_ne_zero hq (show 1 ≤ (3:ℕ) by norm_num)
  have h4nz := k335vcl_sub_ne_zero hq (show 1 ≤ (4:ℕ) by norm_num)
  have h5nz := k335vcl_sub_ne_zero hq (show 1 ≤ (5:ℕ) by norm_num)
  have h6nz := k335vcl_sub_ne_zero hq (show 1 ≤ (6:ℕ) by norm_num)
  have h23 : (q^2-1)*(q^3-1) ≠ 0 := mul_ne_zero h2nz h3nz
  have h234 : (q^2-1)*(q^3-1)*(q^4-1) ≠ 0 := mul_ne_zero h23 h4nz
  have h2345 : (q^2-1)*(q^3-1)*(q^4-1)*(q^5-1) ≠ 0 := mul_ne_zero h234 h5nz
  have hPnz : (q^2-1)*(q^3-1)*(q^4-1)*(q^5-1)*(q^6-1) ≠ 0 := mul_ne_zero h2345 h6nz
  rw [Nat.factorization_mul h15nz hPnz,
    Nat.factorization_mul h2345 h6nz,
    Nat.factorization_mul h234 h5nz,
    Nat.factorization_mul h23 h4nz,
    Nat.factorization_mul h2nz h3nz]
  simp only [Finsupp.add_apply, k335vcl_pow_fact h3, hv3, hv4, hv5, hv6]
  ring

private theorem k335vcl_num_psl7 (hpow : k335vcl_PowHyp) {q : ℕ} (hq : 2 ≤ q)
    (h3 : ¬ 3 ∣ q) (hm : q % 3 = 2) :
    (lieOrderNumerator .PSL 7 q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  have hv3 := k335vcl_v3_sub_odd hpow hq h3 (i := 3) (by norm_num) hm (by norm_num)
  have hv4 := k335vcl_v3_sub_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  have hv5 := k335vcl_v3_sub_odd hpow hq h3 (i := 5) (by norm_num) hm (by norm_num)
  have hv6 := k335vcl_v3_sub_even hpow hq h3 (i := 6) (by norm_num) (by norm_num)
  have hv7 := k335vcl_v3_sub_odd hpow hq h3 (i := 7) (by norm_num) hm (by norm_num)
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 4), add_zero] at hv4
  rw [k335vcl_fact_six] at hv6
  have hnum : lieOrderNumerator .PSL 7 q
      = q^21 * ((q^2-1)*(q^3-1)*(q^4-1)*(q^5-1)*(q^6-1)*(q^7-1)) := by
    simp only [lieOrderNumerator]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 6 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 5 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 4 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 3 + 1 by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num)]
    rw [Finset.Icc_self, Finset.prod_singleton]
  rw [hnum]
  have h21nz : q ^ 21 ≠ 0 := pow_ne_zero 21 (by omega)
  have h2nz := k335vcl_sub_ne_zero hq (show 1 ≤ (2:ℕ) by norm_num)
  have h3nz := k335vcl_sub_ne_zero hq (show 1 ≤ (3:ℕ) by norm_num)
  have h4nz := k335vcl_sub_ne_zero hq (show 1 ≤ (4:ℕ) by norm_num)
  have h5nz := k335vcl_sub_ne_zero hq (show 1 ≤ (5:ℕ) by norm_num)
  have h6nz := k335vcl_sub_ne_zero hq (show 1 ≤ (6:ℕ) by norm_num)
  have h7nz := k335vcl_sub_ne_zero hq (show 1 ≤ (7:ℕ) by norm_num)
  have h23 : (q^2-1)*(q^3-1) ≠ 0 := mul_ne_zero h2nz h3nz
  have h234 : (q^2-1)*(q^3-1)*(q^4-1) ≠ 0 := mul_ne_zero h23 h4nz
  have h2345 : (q^2-1)*(q^3-1)*(q^4-1)*(q^5-1) ≠ 0 := mul_ne_zero h234 h5nz
  have h23456 : (q^2-1)*(q^3-1)*(q^4-1)*(q^5-1)*(q^6-1) ≠ 0 := mul_ne_zero h2345 h6nz
  have hPnz : (q^2-1)*(q^3-1)*(q^4-1)*(q^5-1)*(q^6-1)*(q^7-1) ≠ 0 :=
    mul_ne_zero h23456 h7nz
  rw [Nat.factorization_mul h21nz hPnz,
    Nat.factorization_mul h23456 h7nz,
    Nat.factorization_mul h2345 h6nz,
    Nat.factorization_mul h234 h5nz,
    Nat.factorization_mul h23 h4nz,
    Nat.factorization_mul h2nz h3nz]
  simp only [Finsupp.add_apply, k335vcl_pow_fact h3, hv3, hv4, hv5, hv6, hv7]
  ring

private theorem k335vcl_num_psl67 (hpow : k335vcl_PowHyp) {q n : ℕ} (hq : 2 ≤ q)
    (h3 : ¬ 3 ∣ q) (hn : n = 6 ∨ n = 7) (hm : q % 3 = 2) :
    (lieOrderNumerator .PSL n q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  rcases hn with rfl | rfl
  · exact k335vcl_num_psl6 hpow hq h3 hm
  · exact k335vcl_num_psl7 hpow hq h3 hm

private theorem k335vcl_num_psu6 (hpow : k335vcl_PowHyp) {q : ℕ} (hq : 2 ≤ q)
    (h3 : ¬ 3 ∣ q) (hm : q % 3 = 1) :
    (lieOrderNumerator .PSU 6 q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  have hv3 := k335vcl_v3_add_modone hpow hq h3 (i := 3) (by norm_num) hm
  have hv4 := k335vcl_v3_sub_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  have hv5 := k335vcl_v3_add_modone hpow hq h3 (i := 5) (by norm_num) hm
  have hv6 := k335vcl_v3_sub_even hpow hq h3 (i := 6) (by norm_num) (by norm_num)
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 4), add_zero] at hv4
  rw [k335vcl_fact_six] at hv6
  have hnum : lieOrderNumerator .PSU 6 q
      = q^15 * ((q^2-1)*(q^3+1)*(q^4-1)*(q^5+1)*(q^6-1)) := by
    simp only [lieOrderNumerator]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 5 + 1 by norm_num)]
    rw [if_pos (show Even (6:ℕ) by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 4 + 1 by norm_num)]
    rw [if_neg (show ¬ Even (5:ℕ) by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 3 + 1 by norm_num)]
    rw [if_pos (show Even (4:ℕ) by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num)]
    rw [if_neg (show ¬ Even (3:ℕ) by norm_num)]
    rw [Finset.Icc_self, Finset.prod_singleton]
    rw [if_pos (show Even (2:ℕ) by norm_num)]
  rw [hnum]
  have h15nz : q ^ 15 ≠ 0 := pow_ne_zero 15 (by omega)
  have h2nz := k335vcl_sub_ne_zero hq (show 1 ≤ (2:ℕ) by norm_num)
  have h3nz : q^3+1 ≠ 0 := by positivity
  have h4nz := k335vcl_sub_ne_zero hq (show 1 ≤ (4:ℕ) by norm_num)
  have h5nz : q^5+1 ≠ 0 := by positivity
  have h6nz := k335vcl_sub_ne_zero hq (show 1 ≤ (6:ℕ) by norm_num)
  have h23 : (q^2-1)*(q^3+1) ≠ 0 := mul_ne_zero h2nz h3nz
  have h234 : (q^2-1)*(q^3+1)*(q^4-1) ≠ 0 := mul_ne_zero h23 h4nz
  have h2345 : (q^2-1)*(q^3+1)*(q^4-1)*(q^5+1) ≠ 0 := mul_ne_zero h234 h5nz
  have hPnz : (q^2-1)*(q^3+1)*(q^4-1)*(q^5+1)*(q^6-1) ≠ 0 := mul_ne_zero h2345 h6nz
  rw [Nat.factorization_mul h15nz hPnz,
    Nat.factorization_mul h2345 h6nz,
    Nat.factorization_mul h234 h5nz,
    Nat.factorization_mul h23 h4nz,
    Nat.factorization_mul h2nz h3nz]
  simp only [Finsupp.add_apply, k335vcl_pow_fact h3, hv3, hv4, hv5, hv6]
  ring

private theorem k335vcl_num_psu7 (hpow : k335vcl_PowHyp) {q : ℕ} (hq : 2 ≤ q)
    (h3 : ¬ 3 ∣ q) (hm : q % 3 = 1) :
    (lieOrderNumerator .PSU 7 q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  have hv3 := k335vcl_v3_add_modone hpow hq h3 (i := 3) (by norm_num) hm
  have hv4 := k335vcl_v3_sub_even hpow hq h3 (i := 4) (by norm_num) (by norm_num)
  have hv5 := k335vcl_v3_add_modone hpow hq h3 (i := 5) (by norm_num) hm
  have hv6 := k335vcl_v3_sub_even hpow hq h3 (i := 6) (by norm_num) (by norm_num)
  have hv7 := k335vcl_v3_add_modone hpow hq h3 (i := 7) (by norm_num) hm
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 4), add_zero] at hv4
  rw [k335vcl_fact_six] at hv6
  have hnum : lieOrderNumerator .PSU 7 q
      = q^21 * ((q^2-1)*(q^3+1)*(q^4-1)*(q^5+1)*(q^6-1)*(q^7+1)) := by
    simp only [lieOrderNumerator]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 6 + 1 by norm_num)]
    rw [if_neg (show ¬ Even (7:ℕ) by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 5 + 1 by norm_num)]
    rw [if_pos (show Even (6:ℕ) by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 4 + 1 by norm_num)]
    rw [if_neg (show ¬ Even (5:ℕ) by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 3 + 1 by norm_num)]
    rw [if_pos (show Even (4:ℕ) by norm_num)]
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num)]
    rw [if_neg (show ¬ Even (3:ℕ) by norm_num)]
    rw [Finset.Icc_self, Finset.prod_singleton]
    rw [if_pos (show Even (2:ℕ) by norm_num)]
  rw [hnum]
  have h21nz : q ^ 21 ≠ 0 := pow_ne_zero 21 (by omega)
  have h2nz := k335vcl_sub_ne_zero hq (show 1 ≤ (2:ℕ) by norm_num)
  have h3nz : q^3+1 ≠ 0 := by positivity
  have h4nz := k335vcl_sub_ne_zero hq (show 1 ≤ (4:ℕ) by norm_num)
  have h5nz : q^5+1 ≠ 0 := by positivity
  have h6nz := k335vcl_sub_ne_zero hq (show 1 ≤ (6:ℕ) by norm_num)
  have h7nz : q^7+1 ≠ 0 := by positivity
  have h23 : (q^2-1)*(q^3+1) ≠ 0 := mul_ne_zero h2nz h3nz
  have h234 : (q^2-1)*(q^3+1)*(q^4-1) ≠ 0 := mul_ne_zero h23 h4nz
  have h2345 : (q^2-1)*(q^3+1)*(q^4-1)*(q^5+1) ≠ 0 := mul_ne_zero h234 h5nz
  have h23456 : (q^2-1)*(q^3+1)*(q^4-1)*(q^5+1)*(q^6-1) ≠ 0 := mul_ne_zero h2345 h6nz
  have hPnz : (q^2-1)*(q^3+1)*(q^4-1)*(q^5+1)*(q^6-1)*(q^7+1) ≠ 0 :=
    mul_ne_zero h23456 h7nz
  rw [Nat.factorization_mul h21nz hPnz,
    Nat.factorization_mul h23456 h7nz,
    Nat.factorization_mul h2345 h6nz,
    Nat.factorization_mul h234 h5nz,
    Nat.factorization_mul h23 h4nz,
    Nat.factorization_mul h2nz h3nz]
  simp only [Finsupp.add_apply, k335vcl_pow_fact h3, hv3, hv4, hv5, hv6, hv7]
  ring

private theorem k335vcl_num_psu67 (hpow : k335vcl_PowHyp) {q n : ℕ} (hq : 2 ≤ q)
    (h3 : ¬ 3 ∣ q) (hn : n = 6 ∨ n = 7) (hm : q % 3 = 1) :
    (lieOrderNumerator .PSU n q).factorization 3 = 3 * ((q^2-1).factorization 3) + 1 := by
  rcases hn with rfl | rfl
  · exact k335vcl_num_psu6 hpow hq h3 hm
  · exact k335vcl_num_psu7 hpow hq h3 hm

private theorem k335vcl_finish {card num div A : ℕ}
    (hfac : num = card + div) (hnum : num = 3 * A + 1) (hdiv : div = 0) :
    card = 3 * A + 1 := by
  rw [hnum, hdiv, add_zero] at hfac
  exact hfac.symm

private theorem k335vcl_cases (hpow : k335vcl_PowHyp) {X : Type} [Group X]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hfac : (lieOrderNumerator t n (p^f)).factorization 3
      = (Nat.card X).factorization 3 + (lieOrderDivisor t n (p^f)).factorization 3)
    (hq : 2 ≤ p ^ f) (h3 : ¬ 3 ∣ p ^ f)
    (ht : (t = .PSp ∧ n = 3) ∨ (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4) ∨
      (t = .PSL ∧ n = 4 ∧ p ^ f % 3 = 1) ∨ (t = .PSU ∧ n = 4 ∧ p ^ f % 3 = 2) ∨
      (t = .PSL ∧ (n = 6 ∨ n = 7) ∧ p ^ f % 3 = 2) ∨
      (t = .PSU ∧ (n = 6 ∨ n = 7) ∧ p ^ f % 3 = 1)) :
    (Nat.card X).factorization 3 = 3 * ((p ^ f) ^ 2 - 1).factorization 3 + 1 := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, hm⟩ | ⟨rfl, rfl, hm⟩ |
    ⟨rfl, hn, hm⟩ | ⟨rfl, hn, hm⟩
  · refine k335vcl_finish hfac (k335vcl_num_psp hpow hq h3) ?_
    exact Nat.factorization_eq_zero_of_not_dvd fun hd =>
      (by norm_num : ¬ (3:ℕ) ∣ 2) (Nat.dvd_trans hd (Nat.gcd_dvd_left 2 (p^f - 1)))
  · refine k335vcl_finish hfac (k335vcl_num_psp hpow hq h3) ?_
    exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 2)
  · refine k335vcl_finish hfac (k335vcl_num_pominus hpow hq h3) ?_
    exact Nat.factorization_eq_zero_of_not_dvd fun hd =>
      (by norm_num : ¬ (3:ℕ) ∣ 4) (Nat.dvd_trans hd (Nat.gcd_dvd_left 4 ((p^f)^4 + 1)))
  · refine k335vcl_finish hfac (k335vcl_num_psl4 hpow hq h3 hm) ?_
    exact Nat.factorization_eq_zero_of_not_dvd fun hd =>
      (by norm_num : ¬ (3:ℕ) ∣ 4) (Nat.dvd_trans hd (Nat.gcd_dvd_left 4 (p^f - 1)))
  · refine k335vcl_finish hfac (k335vcl_num_psu4 hpow hq h3 hm) ?_
    exact Nat.factorization_eq_zero_of_not_dvd fun hd =>
      (by norm_num : ¬ (3:ℕ) ∣ 4) (Nat.dvd_trans hd (Nat.gcd_dvd_left 4 (p^f + 1)))
  · refine k335vcl_finish hfac (k335vcl_num_psl67 hpow hq h3 hn hm) ?_
    rcases hn with rfl | rfl
    · exact Nat.factorization_eq_zero_of_not_dvd fun hd =>
        k335vcl_not_dvd_sub_one hm (Nat.dvd_trans hd (Nat.gcd_dvd_right 6 (p^f - 1)))
    · exact Nat.factorization_eq_zero_of_not_dvd fun hd =>
        (by norm_num : ¬ (3:ℕ) ∣ 7) (Nat.dvd_trans hd (Nat.gcd_dvd_left 7 (p^f - 1)))
  · refine k335vcl_finish hfac (k335vcl_num_psu67 hpow hq h3 hn hm) ?_
    rcases hn with rfl | rfl
    · exact Nat.factorization_eq_zero_of_not_dvd fun hd =>
        k335vcl_not_dvd_add_one hm (Nat.dvd_trans hd (Nat.gcd_dvd_right 6 (p^f + 1)))
    · exact Nat.factorization_eq_zero_of_not_dvd fun hd =>
        (by norm_num : ¬ (3:ℕ) ∣ 7) (Nat.dvd_trans hd (Nat.gcd_dvd_left 7 (p^f + 1)))

private theorem k335vcl_core
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) (hp : p ≠ 3)
    (ht : (t = .PSp ∧ n = 3) ∨ (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4) ∨
      (t = .PSL ∧ n = 4 ∧ p ^ f % 3 = 1) ∨ (t = .PSU ∧ n = 4 ∧ p ^ f % 3 = 2) ∨
      (t = .PSL ∧ (n = 6 ∨ n = 7) ∧ p ^ f % 3 = 2) ∨
      (t = .PSU ∧ (n = 6 ∨ n = 7) ∧ p ^ f % 3 = 1)) :
    (Nat.card X).factorization 3 = 3 * ((p ^ f) ^ 2 - 1).factorization 3 + 1 := by
  have hpow' : k335vcl_PowHyp := hpow
  obtain ⟨hpp, hf, -⟩ := h.admissible
  have hq : 2 ≤ p ^ f := by
    have hp2 : 2 ≤ p := hpp.two_le
    have h2f : 2 ≤ 2 ^ f := by
      simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf
    exact le_trans h2f (Nat.pow_le_pow_left hp2 f)
  have h3 : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpp hp
  have hcard := k335_card_lie hO h
  have hfin : Finite X := (hO X t n p f h.admissible h).1
  have hX0 : Nat.card X ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, hfin⟩
  have hd0 : lieOrderDivisor t n (p^f) ≠ 0 := k335vcl_divisor_ne_zero hq t n
  have hfac : (lieOrderNumerator t n (p^f)).factorization 3
      = (Nat.card X).factorization 3 + (lieOrderDivisor t n (p^f)).factorization 3 := by
    rw [← hcard, Nat.factorization_mul hX0 hd0]
    simp only [Finsupp.add_apply]
  exact k335vcl_cases hpow' hfac hq h3 ht

theorem k335_v3_card_classical (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) (hp : p ≠ 3)
    (ht : (t = .PSp ∧ n = 3) ∨ (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4) ∨
      (t = .PSL ∧ n = 4 ∧ p ^ f % 3 = 1) ∨ (t = .PSU ∧ n = 4 ∧ p ^ f % 3 = 2) ∨
      (t = .PSL ∧ (n = 6 ∨ n = 7) ∧ p ^ f % 3 = 2) ∨
      (t = .PSU ∧ (n = 6 ∨ n = 7) ∧ p ^ f % 3 = 1)) :
    (Nat.card X).factorization 3 = 3 * ((p ^ f) ^ 2 - 1).factorization 3 + 1 :=
  k335vcl_core k335_v3_pow hO h hp ht

private theorem k335vev_fac_mul3 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

private theorem k335vev_pow_fac_zero {q N : ℕ} (h3 : ¬ 3 ∣ q) : (q ^ N).factorization 3 = 0 := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.factorization_eq_zero_of_not_dvd h3, mul_zero]

private theorem k335vev_pow_sub_ne_zero {q i : ℕ} (hq : 2 ≤ q) (hi : 1 ≤ i) :
    q ^ i - 1 ≠ 0 := by
  have h1 : 1 < q ^ i := by
    calc 1 < 2 := by norm_num
      _ ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ i := Nat.pow_le_pow_right (by omega) hi
  omega

private theorem k335vev_pow_add_ne_zero (q i : ℕ) : q ^ i + 1 ≠ 0 := by positivity

private theorem k335vev_gcd_ne_zero_left {m q : ℕ} (hm : 0 < m) : Nat.gcd m q ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m q) hm)

private theorem k335vev_gcd_fac_zero {m q : ℕ} (hm : ¬ 3 ∣ m) :
    (Nat.gcd m q).factorization 3 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  exact hm (Nat.dvd_trans hd (Nat.gcd_dvd_left m q))

private theorem k335vev_three_dvd_sub {q : ℕ} (h1 : 1 ≤ q) (h : q % 3 = 1) : 3 ∣ q - 1 := by
  have hme : q ≡ 1 [MOD 3] := by
    simp only [Nat.ModEq]
    rw [h, Nat.mod_eq_of_lt (by norm_num : 1 < 3)]
  exact (Nat.modEq_iff_dvd' h1).mp hme.symm

private theorem k335vev_three_dvd_add {q : ℕ} (h : q % 3 = 2) : 3 ∣ q + 1 := by
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, h]

private theorem k335vev_fac2 : (2 : ℕ).factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by norm_num)

private theorem k335vev_fac3 : (3 : ℕ).factorization 3 = 1 :=
  Nat.Prime.factorization_self Nat.prime_three

private theorem k335vev_fac4 : (4 : ℕ).factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by norm_num)

private theorem k335vev_fac6 : (6 : ℕ).factorization 3 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, k335vev_fac_mul3 (by norm_num) (by norm_num),
    k335vev_fac2, k335vev_fac3, zero_add]

private theorem k335vev_fac12 : (12 : ℕ).factorization 3 = 1 := by
  rw [show (12 : ℕ) = 4 * 3 from rfl, k335vev_fac_mul3 (by norm_num) (by norm_num),
    k335vev_fac4, k335vev_fac3, zero_add]

private theorem k335vev_prod_2_3 (g : ℕ → ℕ) :
    (∏ i ∈ Finset.Icc 2 3, g i) = g 2 * g 3 := by
  rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1) g, Finset.Icc_self,
    Finset.prod_singleton]

private theorem k335vev_prod_2_4 (g : ℕ → ℕ) :
    (∏ i ∈ Finset.Icc 2 4, g i) = g 2 * g 3 * g 4 := by
  rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1) g, k335vev_prod_2_3]

private theorem k335vev_prod_2_5 (g : ℕ → ℕ) :
    (∏ i ∈ Finset.Icc 2 5, g i) = g 2 * g 3 * g 4 * g 5 := by
  rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4 + 1) g, k335vev_prod_2_4]

private theorem k335vev_prod_1_2 (g : ℕ → ℕ) :
    (∏ i ∈ Finset.Icc 1 2, g i) = g 1 * g 2 := by
  rw [Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 1 + 1) g, Finset.Icc_self,
    Finset.prod_singleton]

private theorem k335vev_psu_prod_2_3 (q : ℕ) :
    (∏ i ∈ Finset.Icc 2 3, (if Even i then q ^ i - 1 else q ^ i + 1)) =
      (q ^ 2 - 1) * (q ^ 3 + 1) := by
  rw [k335vev_prod_2_3 (fun i => if Even i then q ^ i - 1 else q ^ i + 1),
    if_pos (show Even 2 by norm_num), if_neg (show ¬ Even 3 by norm_num)]

private theorem k335vev_psu_prod_2_4 (q : ℕ) :
    (∏ i ∈ Finset.Icc 2 4, (if Even i then q ^ i - 1 else q ^ i + 1)) =
      (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) := by
  rw [k335vev_prod_2_4 (fun i => if Even i then q ^ i - 1 else q ^ i + 1),
    if_pos (show Even 2 by norm_num), if_neg (show ¬ Even 3 by norm_num),
    if_pos (show Even 4 by norm_num)]

private theorem k335vev_psu_prod_2_5 (q : ℕ) :
    (∏ i ∈ Finset.Icc 2 5, (if Even i then q ^ i - 1 else q ^ i + 1)) =
      (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) := by
  rw [k335vev_prod_2_5 (fun i => if Even i then q ^ i - 1 else q ^ i + 1),
    if_pos (show Even 2 by norm_num), if_neg (show ¬ Even 3 by norm_num),
    if_pos (show Even 4 by norm_num), if_neg (show ¬ Even 5 by norm_num)]

private theorem k335vev_psp_prod_1_2 (q : ℕ) :
    (∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1)) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
  rw [k335vev_prod_1_2 (fun i => q ^ (2 * i) - 1)]

private theorem k335vev_num2_fac {q N : ℕ} (hq0 : q ≠ 0) (h3 : ¬ 3 ∣ q) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (q ^ N * (a * b)).factorization 3 = a.factorization 3 + b.factorization 3 := by
  rw [k335vev_fac_mul3 (pow_ne_zero N hq0) (mul_ne_zero ha hb),
    k335vev_pow_fac_zero h3, zero_add, k335vev_fac_mul3 ha hb]

private theorem k335vev_num3_fac {q N : ℕ} (hq0 : q ≠ 0) (h3 : ¬ 3 ∣ q) {a b c : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (q ^ N * (a * b * c)).factorization 3 =
      a.factorization 3 + b.factorization 3 + c.factorization 3 := by
  rw [k335vev_fac_mul3 (pow_ne_zero N hq0) (mul_ne_zero (mul_ne_zero ha hb) hc),
    k335vev_pow_fac_zero h3, zero_add,
    k335vev_fac_mul3 (mul_ne_zero ha hb) hc, k335vev_fac_mul3 ha hb]

private theorem k335vev_num4_fac {q N : ℕ} (hq0 : q ≠ 0) (h3 : ¬ 3 ∣ q) {a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (q ^ N * (a * b * c * d)).factorization 3 =
      a.factorization 3 + b.factorization 3 + c.factorization 3 + d.factorization 3 := by
  rw [k335vev_fac_mul3 (pow_ne_zero N hq0)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd),
    k335vev_pow_fac_zero h3, zero_add,
    k335vev_fac_mul3 (mul_ne_zero (mul_ne_zero ha hb) hc) hd,
    k335vev_fac_mul3 (mul_ne_zero ha hb) hc, k335vev_fac_mul3 ha hb]

private theorem k335vev_factor (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f)
    (hdiv : lieOrderDivisor t n (p ^ f) ≠ 0) :
    (Nat.card X).factorization 3 + (lieOrderDivisor t n (p ^ f)).factorization 3 =
      (lieOrderNumerator t n (p ^ f)).factorization 3 := by
  have hfin : Finite X := (hO X t n p f h.admissible h).1
  have hcard : Nat.card X ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, hfin⟩
  have hmul := k335_card_lie hO h
  have := congrArg (fun m : ℕ => m.factorization 3) hmul
  rwa [Nat.factorization_mul hcard hdiv, Finsupp.add_apply] at this

private theorem k335vev_psl3
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 3 p f) (hp : p ≠ 3) (hmod : p ^ f % 3 = 1) :
    Even ((Nat.card X).factorization 3) := by
  have hpP : p.Prime := h.admissible.1
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hp2 : 2 ≤ p := hpP.two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf1
  have hq0 : p ^ f ≠ 0 := by omega
  have h3q : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpP hp
  have hdiv_eq : lieOrderDivisor .PSL 3 (p ^ f) = 3 := by
    rw [show lieOrderDivisor .PSL 3 (p ^ f) = Nat.gcd 3 (p ^ f - 1) from rfl,
      Nat.gcd_eq_left (k335vev_three_dvd_sub (by omega) hmod)]
  have hm := k335vev_factor hO h (by rw [hdiv_eq]; norm_num)
  have hdivfac : (lieOrderDivisor .PSL 3 (p ^ f)).factorization 3 = 1 := by
    rw [hdiv_eq, k335vev_fac3]
  have hnum_expand : lieOrderNumerator .PSL 3 (p ^ f) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) := by
    show (p ^ f) ^ (3 * (3 - 1) / 2) * (∏ i ∈ Finset.Icc 2 3, ((p ^ f) ^ i - 1)) = _
    rw [k335vev_prod_2_3 (fun i => (p ^ f) ^ i - 1)]
  have h3v : ((p ^ f) ^ 3 - 1).factorization 3 =
      ((p ^ f) ^ 2 - 1).factorization 3 + 1 := by
    have hh := (hpow hq2 h3q (i := 3) (by norm_num)).1
    rw [if_pos (Or.inl hmod), k335vev_fac3] at hh
    exact hh
  have hnumfac : (lieOrderNumerator .PSL 3 (p ^ f)).factorization 3 =
      2 * ((p ^ f) ^ 2 - 1).factorization 3 + 1 := by
    rw [hnum_expand, k335vev_num2_fac hq0 h3q
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_sub_ne_zero hq2 (by norm_num)), h3v]
    ring
  rw [hdivfac, hnumfac] at hm
  exact ⟨((p ^ f) ^ 2 - 1).factorization 3, by omega⟩

private theorem k335vev_psu3
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSU 3 p f) (hp : p ≠ 3) (hmod : p ^ f % 3 = 2) :
    Even ((Nat.card X).factorization 3) := by
  have hpP : p.Prime := h.admissible.1
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hp2 : 2 ≤ p := hpP.two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf1
  have hq0 : p ^ f ≠ 0 := by omega
  have h3q : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpP hp
  have hdiv_eq : lieOrderDivisor .PSU 3 (p ^ f) = 3 := by
    rw [show lieOrderDivisor .PSU 3 (p ^ f) = Nat.gcd 3 (p ^ f + 1) from rfl,
      Nat.gcd_eq_left (k335vev_three_dvd_add hmod)]
  have hm := k335vev_factor hO h (by rw [hdiv_eq]; norm_num)
  have hdivfac : (lieOrderDivisor .PSU 3 (p ^ f)).factorization 3 = 1 := by
    rw [hdiv_eq, k335vev_fac3]
  have hnum_expand : lieOrderNumerator .PSU 3 (p ^ f) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
    show (p ^ f) ^ (3 * (3 - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 3, (if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1)) = _
    rw [k335vev_psu_prod_2_3]
  have h3v : ((p ^ f) ^ 3 + 1).factorization 3 =
      ((p ^ f) ^ 2 - 1).factorization 3 + 1 := by
    have hh := (hpow hq2 h3q (i := 3) (by norm_num)).2
    rw [if_pos ⟨hmod, (show Odd 3 by norm_num)⟩, k335vev_fac3] at hh
    exact hh
  have hnumfac : (lieOrderNumerator .PSU 3 (p ^ f)).factorization 3 =
      2 * ((p ^ f) ^ 2 - 1).factorization 3 + 1 := by
    rw [hnum_expand, k335vev_num2_fac hq0 h3q
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_add_ne_zero (p ^ f) 3), h3v]
    ring
  rw [hdivfac, hnumfac] at hm
  exact ⟨((p ^ f) ^ 2 - 1).factorization 3, by omega⟩

private theorem k335vev_psp2
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSp 2 p f) (hp : p ≠ 3) :
    Even ((Nat.card X).factorization 3) := by
  have hpP : p.Prime := h.admissible.1
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hp2 : 2 ≤ p := hpP.two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf1
  have hq0 : p ^ f ≠ 0 := by omega
  have h3q : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpP hp
  have hdiv_eq : lieOrderDivisor .PSp 2 (p ^ f) = Nat.gcd 2 (p ^ f - 1) := rfl
  have hm := k335vev_factor hO h (by rw [hdiv_eq]; exact k335vev_gcd_ne_zero_left (by norm_num))
  have hdivfac : (lieOrderDivisor .PSp 2 (p ^ f)).factorization 3 = 0 := by
    rw [hdiv_eq]; exact k335vev_gcd_fac_zero (by norm_num : ¬ 3 ∣ 2)
  have hnum_expand : lieOrderNumerator .PSp 2 (p ^ f) =
      (p ^ f) ^ (2 ^ 2) * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
    show (p ^ f) ^ (2 ^ 2) * (∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1)) = _
    rw [k335vev_psp_prod_1_2]
  have h4v : ((p ^ f) ^ 4 - 1).factorization 3 = ((p ^ f) ^ 2 - 1).factorization 3 := by
    have hh := (hpow hq2 h3q (i := 4) (by norm_num)).1
    rw [if_pos (Or.inr (show Even 4 by norm_num)), k335vev_fac4, add_zero] at hh
    exact hh
  have hnumfac : (lieOrderNumerator .PSp 2 (p ^ f)).factorization 3 =
      2 * ((p ^ f) ^ 2 - 1).factorization 3 := by
    rw [hnum_expand, k335vev_num2_fac hq0 h3q
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_sub_ne_zero hq2 (by norm_num)), h4v]
    ring
  rw [hdivfac, hnumfac] at hm
  exact ⟨((p ^ f) ^ 2 - 1).factorization 3, by omega⟩

private theorem k335vev_triality
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .trialityD4 n p f) (hp : p ≠ 3) :
    Even ((Nat.card X).factorization 3) := by
  have hpP : p.Prime := h.admissible.1
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hp2 : 2 ≤ p := hpP.two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf1
  have hq0 : p ^ f ≠ 0 := by omega
  have h3q : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpP hp
  have hdiv_eq : lieOrderDivisor .trialityD4 n (p ^ f) = 1 := rfl
  have hm := k335vev_factor hO h (by rw [hdiv_eq]; norm_num)
  have hdivfac : (lieOrderDivisor .trialityD4 n (p ^ f)).factorization 3 = 0 := by
    rw [hdiv_eq]; exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 1)
  have hnum_expand : lieOrderNumerator .trialityD4 n (p ^ f) =
      (p ^ f) ^ 12 * ((((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1) * ((p ^ f) ^ 6 - 1)) *
        ((p ^ f) ^ 2 - 1)) := by
    show (p ^ f) ^ 12 * ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1) * ((p ^ f) ^ 6 - 1) *
        ((p ^ f) ^ 2 - 1) = _
    ring
  have h6v : ((p ^ f) ^ 6 - 1).factorization 3 =
      ((p ^ f) ^ 2 - 1).factorization 3 + 1 := by
    have hh := (hpow hq2 h3q (i := 6) (by norm_num)).1
    rw [if_pos (Or.inr (show Even 6 by norm_num)), k335vev_fac6] at hh
    exact hh
  have htri : ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1).factorization 3 = 1 := by
    have h12 : ((p ^ f) ^ 12 - 1).factorization 3 =
        ((p ^ f) ^ 2 - 1).factorization 3 + 1 := by
      have hh := (hpow hq2 h3q (i := 12) (by norm_num)).1
      rw [if_pos (Or.inr (show Even 12 by norm_num)), k335vev_fac12] at hh
      exact hh
    have h4 : ((p ^ f) ^ 4 - 1).factorization 3 = ((p ^ f) ^ 2 - 1).factorization 3 := by
      have hh := (hpow hq2 h3q (i := 4) (by norm_num)).1
      rw [if_pos (Or.inr (show Even 4 by norm_num)), k335vev_fac4, add_zero] at hh
      exact hh
    have hprod : ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1) * ((p ^ f) ^ 4 - 1) = (p ^ f) ^ 12 - 1 := by
      have hq4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow 4 (p ^ f) (by omega)
      have hq12 : 1 ≤ (p ^ f) ^ 12 := Nat.one_le_pow 12 (p ^ f) (by omega)
      zify [hq4, hq12]
      ring
    have hfac := congrArg (fun m : ℕ => m.factorization 3) hprod
    rw [k335vev_fac_mul3 (by positivity)
      (k335vev_pow_sub_ne_zero hq2 (by norm_num)), h4, h12] at hfac
    omega
  have hnumfac : (lieOrderNumerator .trialityD4 n (p ^ f)).factorization 3 =
      2 * ((p ^ f) ^ 2 - 1).factorization 3 + 2 := by
    rw [hnum_expand, k335vev_num3_fac hq0 h3q (by positivity)
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_sub_ne_zero hq2 (by norm_num)), htri, h6v]
    ring
  rw [hdivfac, hnumfac] at hm
  exact ⟨((p ^ f) ^ 2 - 1).factorization 3 + 1, by omega⟩

private theorem k335vev_psl4
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 4 p f) (hp : p ≠ 3) (hmod : p ^ f % 3 = 2) :
    Even ((Nat.card X).factorization 3) := by
  have hpP : p.Prime := h.admissible.1
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hp2 : 2 ≤ p := hpP.two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf1
  have hq0 : p ^ f ≠ 0 := by omega
  have h3q : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpP hp
  have hdiv_eq : lieOrderDivisor .PSL 4 (p ^ f) = Nat.gcd 4 (p ^ f - 1) := rfl
  have hm := k335vev_factor hO h (by rw [hdiv_eq]; exact k335vev_gcd_ne_zero_left (by norm_num))
  have hdivfac : (lieOrderDivisor .PSL 4 (p ^ f)).factorization 3 = 0 := by
    rw [hdiv_eq]; exact k335vev_gcd_fac_zero (by norm_num : ¬ 3 ∣ 4)
  have hnum_expand : lieOrderNumerator .PSL 4 (p ^ f) =
      (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)) := by
    show (p ^ f) ^ (4 * (4 - 1) / 2) * (∏ i ∈ Finset.Icc 2 4, ((p ^ f) ^ i - 1)) = _
    rw [k335vev_prod_2_4 (fun i => (p ^ f) ^ i - 1)]
  have h3v : ((p ^ f) ^ 3 - 1).factorization 3 = 0 := by
    have hh := (hpow hq2 h3q (i := 3) (by norm_num)).1
    rw [if_neg (by
      rintro (h | h)
      · omega
      · exact (by norm_num : ¬ Even 3) h)] at hh
    exact hh
  have h4v : ((p ^ f) ^ 4 - 1).factorization 3 = ((p ^ f) ^ 2 - 1).factorization 3 := by
    have hh := (hpow hq2 h3q (i := 4) (by norm_num)).1
    rw [if_pos (Or.inr (show Even 4 by norm_num)), k335vev_fac4, add_zero] at hh
    exact hh
  have hnumfac : (lieOrderNumerator .PSL 4 (p ^ f)).factorization 3 =
      2 * ((p ^ f) ^ 2 - 1).factorization 3 := by
    rw [hnum_expand, k335vev_num3_fac hq0 h3q
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_sub_ne_zero hq2 (by norm_num)), h3v, h4v]
    ring
  rw [hdivfac, hnumfac] at hm
  exact ⟨((p ^ f) ^ 2 - 1).factorization 3, by omega⟩

private theorem k335vev_psu4
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSU 4 p f) (hp : p ≠ 3) (hmod : p ^ f % 3 = 1) :
    Even ((Nat.card X).factorization 3) := by
  have hpP : p.Prime := h.admissible.1
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hp2 : 2 ≤ p := hpP.two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf1
  have hq0 : p ^ f ≠ 0 := by omega
  have h3q : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpP hp
  have hdiv_eq : lieOrderDivisor .PSU 4 (p ^ f) = Nat.gcd 4 (p ^ f + 1) := rfl
  have hm := k335vev_factor hO h (by rw [hdiv_eq]; exact k335vev_gcd_ne_zero_left (by norm_num))
  have hdivfac : (lieOrderDivisor .PSU 4 (p ^ f)).factorization 3 = 0 := by
    rw [hdiv_eq]; exact k335vev_gcd_fac_zero (by norm_num : ¬ 3 ∣ 4)
  have hnum_expand : lieOrderNumerator .PSU 4 (p ^ f) =
      (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) := by
    show (p ^ f) ^ (4 * (4 - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 4, (if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1)) = _
    rw [k335vev_psu_prod_2_4]
  have h3v : ((p ^ f) ^ 3 + 1).factorization 3 = 0 := by
    have hh := (hpow hq2 h3q (i := 3) (by norm_num)).2
    rw [if_neg (by rintro ⟨h, -⟩; omega)] at hh
    exact hh
  have h4v : ((p ^ f) ^ 4 - 1).factorization 3 = ((p ^ f) ^ 2 - 1).factorization 3 := by
    have hh := (hpow hq2 h3q (i := 4) (by norm_num)).1
    rw [if_pos (Or.inr (show Even 4 by norm_num)), k335vev_fac4, add_zero] at hh
    exact hh
  have hnumfac : (lieOrderNumerator .PSU 4 (p ^ f)).factorization 3 =
      2 * ((p ^ f) ^ 2 - 1).factorization 3 := by
    rw [hnum_expand, k335vev_num3_fac hq0 h3q
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_add_ne_zero (p ^ f) 3)
      (k335vev_pow_sub_ne_zero hq2 (by norm_num)), h3v, h4v]
    ring
  rw [hdivfac, hnumfac] at hm
  exact ⟨((p ^ f) ^ 2 - 1).factorization 3, by omega⟩

private theorem k335vev_psl5
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 5 p f) (hp : p ≠ 3) (hmod : p ^ f % 3 = 2) :
    Even ((Nat.card X).factorization 3) := by
  have hpP : p.Prime := h.admissible.1
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hp2 : 2 ≤ p := hpP.two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf1
  have hq0 : p ^ f ≠ 0 := by omega
  have h3q : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpP hp
  have hdiv_eq : lieOrderDivisor .PSL 5 (p ^ f) = Nat.gcd 5 (p ^ f - 1) := rfl
  have hm := k335vev_factor hO h (by rw [hdiv_eq]; exact k335vev_gcd_ne_zero_left (by norm_num))
  have hdivfac : (lieOrderDivisor .PSL 5 (p ^ f)).factorization 3 = 0 := by
    rw [hdiv_eq]; exact k335vev_gcd_fac_zero (by norm_num : ¬ 3 ∣ 5)
  have hnum_expand : lieOrderNumerator .PSL 5 (p ^ f) =
      (p ^ f) ^ 10 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1) *
        ((p ^ f) ^ 5 - 1)) := by
    show (p ^ f) ^ (5 * (5 - 1) / 2) * (∏ i ∈ Finset.Icc 2 5, ((p ^ f) ^ i - 1)) = _
    rw [k335vev_prod_2_5 (fun i => (p ^ f) ^ i - 1)]
  have h3v : ((p ^ f) ^ 3 - 1).factorization 3 = 0 := by
    have hh := (hpow hq2 h3q (i := 3) (by norm_num)).1
    rw [if_neg (by
      rintro (h | h)
      · omega
      · exact (by norm_num : ¬ Even 3) h)] at hh
    exact hh
  have h5v : ((p ^ f) ^ 5 - 1).factorization 3 = 0 := by
    have hh := (hpow hq2 h3q (i := 5) (by norm_num)).1
    rw [if_neg (by
      rintro (h | h)
      · omega
      · exact (by norm_num : ¬ Even 5) h)] at hh
    exact hh
  have h4v : ((p ^ f) ^ 4 - 1).factorization 3 = ((p ^ f) ^ 2 - 1).factorization 3 := by
    have hh := (hpow hq2 h3q (i := 4) (by norm_num)).1
    rw [if_pos (Or.inr (show Even 4 by norm_num)), k335vev_fac4, add_zero] at hh
    exact hh
  have hnumfac : (lieOrderNumerator .PSL 5 (p ^ f)).factorization 3 =
      2 * ((p ^ f) ^ 2 - 1).factorization 3 := by
    rw [hnum_expand, k335vev_num4_fac hq0 h3q
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_sub_ne_zero hq2 (by norm_num)), h3v, h4v, h5v]
    ring
  rw [hdivfac, hnumfac] at hm
  exact ⟨((p ^ f) ^ 2 - 1).factorization 3, by omega⟩

private theorem k335vev_psu5
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSU 5 p f) (hp : p ≠ 3) (hmod : p ^ f % 3 = 1) :
    Even ((Nat.card X).factorization 3) := by
  have hpP : p.Prime := h.admissible.1
  have hf1 : 1 ≤ f := h.admissible.2.1
  have hp2 : 2 ≤ p := hpP.two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf1
  have hq0 : p ^ f ≠ 0 := by omega
  have h3q : ¬ 3 ∣ p ^ f := k335_three_not_dvd hpP hp
  have hdiv_eq : lieOrderDivisor .PSU 5 (p ^ f) = Nat.gcd 5 (p ^ f + 1) := rfl
  have hm := k335vev_factor hO h (by rw [hdiv_eq]; exact k335vev_gcd_ne_zero_left (by norm_num))
  have hdivfac : (lieOrderDivisor .PSU 5 (p ^ f)).factorization 3 = 0 := by
    rw [hdiv_eq]; exact k335vev_gcd_fac_zero (by norm_num : ¬ 3 ∣ 5)
  have hnum_expand : lieOrderNumerator .PSU 5 (p ^ f) =
      (p ^ f) ^ 10 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) *
        ((p ^ f) ^ 5 + 1)) := by
    show (p ^ f) ^ (5 * (5 - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 5, (if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1)) = _
    rw [k335vev_psu_prod_2_5]
  have h3v : ((p ^ f) ^ 3 + 1).factorization 3 = 0 := by
    have hh := (hpow hq2 h3q (i := 3) (by norm_num)).2
    rw [if_neg (by rintro ⟨h, -⟩; omega)] at hh
    exact hh
  have h5v : ((p ^ f) ^ 5 + 1).factorization 3 = 0 := by
    have hh := (hpow hq2 h3q (i := 5) (by norm_num)).2
    rw [if_neg (by rintro ⟨h, -⟩; omega)] at hh
    exact hh
  have h4v : ((p ^ f) ^ 4 - 1).factorization 3 = ((p ^ f) ^ 2 - 1).factorization 3 := by
    have hh := (hpow hq2 h3q (i := 4) (by norm_num)).1
    rw [if_pos (Or.inr (show Even 4 by norm_num)), k335vev_fac4, add_zero] at hh
    exact hh
  have hnumfac : (lieOrderNumerator .PSU 5 (p ^ f)).factorization 3 =
      2 * ((p ^ f) ^ 2 - 1).factorization 3 := by
    rw [hnum_expand, k335vev_num4_fac hq0 h3q
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_add_ne_zero (p ^ f) 3)
      (k335vev_pow_sub_ne_zero hq2 (by norm_num))
      (k335vev_pow_add_ne_zero (p ^ f) 5), h3v, h4v, h5v]
    ring
  rw [hdivfac, hnumfac] at hm
  exact ⟨((p ^ f) ^ 2 - 1).factorization 3, by omega⟩

private theorem k335vev_core
    (hpow : ∀ {q : ℕ}, 2 ≤ q → ¬ 3 ∣ q → ∀ {i : ℕ}, 1 ≤ i →
      (q ^ i - 1).factorization 3 =
          (if q % 3 = 1 ∨ Even i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0) ∧
        (q ^ i + 1).factorization 3 =
          (if q % 3 = 2 ∧ Odd i then (q ^ 2 - 1).factorization 3 + i.factorization 3 else 0))
    (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) (hp : p ≠ 3)
    (ht : (t = .PSL ∧ n = 3 ∧ p ^ f % 3 = 1) ∨ (t = .PSU ∧ n = 3 ∧ p ^ f % 3 = 2) ∨
      (t = .PSp ∧ n = 2) ∨ t = .trialityD4 ∨
      (t = .PSL ∧ n = 4 ∧ p ^ f % 3 = 2) ∨ (t = .PSU ∧ n = 4 ∧ p ^ f % 3 = 1) ∨
      (t = .PSL ∧ n = 5 ∧ p ^ f % 3 = 2) ∨ (t = .PSU ∧ n = 5 ∧ p ^ f % 3 = 1)) :
    Even ((Nat.card X).factorization 3) := by
  rcases ht with ⟨rfl, rfl, hmod⟩ | ⟨rfl, rfl, hmod⟩ | ⟨rfl, rfl⟩ | rfl |
    ⟨rfl, rfl, hmod⟩ | ⟨rfl, rfl, hmod⟩ | ⟨rfl, rfl, hmod⟩ | ⟨rfl, rfl, hmod⟩
  · exact k335vev_psl3 hpow hO h hp hmod
  · exact k335vev_psu3 hpow hO h hp hmod
  · exact k335vev_psp2 hpow hO h hp
  · exact k335vev_triality hpow hO h hp
  · exact k335vev_psl4 hpow hO h hp hmod
  · exact k335vev_psu4 hpow hO h hp hmod
  · exact k335vev_psl5 hpow hO h hp hmod
  · exact k335vev_psu5 hpow hO h hp hmod

theorem k335_even_v3 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) (hp : p ≠ 3)
    (ht : (t = .PSL ∧ n = 3 ∧ p ^ f % 3 = 1) ∨ (t = .PSU ∧ n = 3 ∧ p ^ f % 3 = 2) ∨
      (t = .PSp ∧ n = 2) ∨ t = .trialityD4 ∨
      (t = .PSL ∧ n = 4 ∧ p ^ f % 3 = 2) ∨ (t = .PSU ∧ n = 4 ∧ p ^ f % 3 = 1) ∨
      (t = .PSL ∧ n = 5 ∧ p ^ f % 3 = 2) ∨ (t = .PSU ∧ n = 5 ∧ p ^ f % 3 = 1)) :
    Even ((Nat.card X).factorization 3) :=
  k335vev_core k335_v3_pow hO h hp ht

theorem k335_even_v3_char_three (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : CFSG.Open.StatedLieTag} {n f : ℕ} (h : LieModel X t n 3 f)
    (ht : (t = .PSp ∧ n = 2) ∨ t = .G2 ∨ t = .trialityD4) :
    Even ((Nat.card X).factorization 3) := by
  rw [(hO X t n 3 f h.admissible h).2.2]
  rcases ht with ⟨rfl, rfl⟩ | rfl | rfl
  · exact (show Even (lieSylowExponent .PSp 2) by decide).mul_right f
  · rw [show lieSylowExponent .G2 n = 6 from rfl]
    exact (show Even 6 by decide).mul_right f
  · rw [show lieSylowExponent .trialityD4 n = 12 from rfl]
    exact (show Even 12 by decide).mul_right f

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
