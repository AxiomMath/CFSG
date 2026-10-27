module

public import CFSG.Quasithin.Background.S1549DL3N

public section

namespace CFSG.Quasithin.H13.NQRigid

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Arith

theorem psl_mono {s t : ℕ} (h : s ≤ t) : s * (s ^ 2 - 1) ≤ t * (t ^ 2 - 1) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

theorem psl_strict {s t : ℕ} (h : s < t) (ht : 2 ≤ t) : s * (s ^ 2 - 1) < t * (t ^ 2 - 1) := by
  have h1 : s * (s ^ 2 - 1) ≤ s * (t ^ 2 - 1) :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.pow_le_pow_left h.le 2) 1)
  have h2 : 0 < t ^ 2 - 1 := by
    have : 4 ≤ t ^ 2 := by nlinarith
    omega
  have h3 : s * (t ^ 2 - 1) < t * (t ^ 2 - 1) := by nlinarith
  omega

theorem psl_ne_of_between {s a c : ℕ} (h1 : a * (a ^ 2 - 1) < c)
    (h2 : c < (a + 1) * ((a + 1) ^ 2 - 1)) : s * (s ^ 2 - 1) ≠ c := by
  intro h
  rcases le_or_gt s a with hs | hs
  · have := psl_mono hs
    omega
  · have := psl_mono (show a + 1 ≤ s from hs)
    omega

theorem psl_eq_of_eq {s a : ℕ} (h : s * (s ^ 2 - 1) = a * (a ^ 2 - 1)) (ha : 2 ≤ a) : s = a := by
  rcases lt_trichotomy s a with hs | hs | hs
  · have := psl_strict hs ha
    omega
  · exact hs
  · have := psl_strict hs (by omega)
    omega

theorem sq_sub_one_eq (q : ℕ) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  rcases q with _ | q
  · simp
  · simp only [Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring

theorem cube_sub_one_eq (q : ℕ) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  rcases q with _ | q
  · simp
  · simp only [Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring

theorem fourth_sub_one_eq (q : ℕ) : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · obtain ⟨r, hr⟩ : ∃ r, q ^ 2 = r + 1 := ⟨q ^ 2 - 1, by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
      omega⟩
    have h4 : q ^ 4 = (q ^ 2) ^ 2 := by ring
    rw [h4, hr, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring

theorem sixth_sub_one_eq (q : ℕ) : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · obtain ⟨r, hr⟩ : ∃ r, q ^ 2 = r + 1 := ⟨q ^ 2 - 1, by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
      omega⟩
    have h6 : q ^ 6 = (q ^ 2) ^ 3 := by ring
    have h4 : q ^ 4 = (q ^ 2) ^ 2 := by ring
    rw [h6, h4, hr, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring

variable {s : ℕ}

theorem not_dvd_two_pow (hs : s.Prime) (hs5 : 5 ≤ s) (n : ℕ) : ¬ s ∣ 2 ^ n := fun h => by
  have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h)
  omega

theorem prime_dvd_of_dvd_two_mul (hs : s.Prime) (hs5 : 5 ≤ s) {q x : ℕ} (hsq : ¬ s ∣ q)
    (h : s ∣ 2 * (q * x)) : s ∣ x := by
  rcases (Nat.Prime.dvd_mul hs).mp h with h2 | h2
  · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  · rcases (Nat.Prime.dvd_mul hs).mp h2 with h3 | h3
    · exact absurd h3 hsq
    · exact h3

theorem le_of_prime_dvd {x y : ℕ} (hy : 0 < y) (h : s ∣ x * y) (hx : s ∣ x → s ≤ y)
    (hs : s.Prime) : s ≤ y := by
  rcases (Nat.Prime.dvd_mul hs).mp h with h1 | h1
  · exact hx h1
  · exact Nat.le_of_dvd hy h1

theorem psl2_eq_sl2 (hs : s.Prime) (hs5 : 5 ≤ s) {q : ℕ} (hq : 2 ≤ q) (hsq : ¬ s ∣ q)
    (h : s * (s ^ 2 - 1) = 2 * (q * (q ^ 2 - 1))) : q = 4 ∧ s = 5 := by
  have hdvd : s ∣ 2 * (q * (q ^ 2 - 1)) := ⟨s ^ 2 - 1, h.symm⟩
  have h1 := prime_dvd_of_dvd_two_mul hs hs5 hsq hdvd
  rw [sq_sub_one_eq] at h1
  have hsle : s ≤ q + 1 := le_of_prime_dvd (by omega) h1
    (fun h2 => (Nat.le_of_dvd (by omega) h2).trans (by omega)) hs
  have hq4 : q ≤ 4 := by
    by_contra hq4
    push Not at hq4
    have h2 := psl_mono hsle
    have h3 : (q + 1) * ((q + 1) ^ 2 - 1) < 2 * (q * (q ^ 2 - 1)) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 5 := ⟨q - 5, by omega⟩
      have e1 : (r + 5 + 1) ^ 2 - 1 = (r + 5) * (r + 7) := by
        apply Nat.sub_eq_of_eq_add
        ring
      have e2 : (r + 5) ^ 2 - 1 = (r + 4) * (r + 6) := by
        apply Nat.sub_eq_of_eq_add
        ring
      rw [e1, e2]
      ring_nf
      nlinarith
    omega
  have h5 := psl_mono hs5
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 := by omega
  rcases hcases with rfl | rfl | rfl
  · norm_num at h h5
    omega
  · norm_num at h h5
    omega
  · exact ⟨rfl, psl_eq_of_eq (a := 5) (h.trans (by norm_num)) (by norm_num)⟩

theorem psl2_eq_sl3 (hs : s.Prime) (hs5 : 5 ≤ s) {q : ℕ} (hq : 2 ≤ q) (hsq : ¬ s ∣ q)
    (h : s * (s ^ 2 - 1) = 2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))) : q = 2 ∧ s = 7 := by
  have hsq3 : ¬ s ∣ q ^ 3 := fun h3 => hsq (hs.dvd_of_dvd_pow h3)
  have hdvd : s ∣ 2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) := ⟨s ^ 2 - 1, h.symm⟩
  have h1 := prime_dvd_of_dvd_two_mul hs hs5 hsq3 hdvd
  have hsle : s ≤ q ^ 2 + q + 1 := by
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · rw [sq_sub_one_eq] at h2
      have := le_of_prime_dvd (by omega) h2
        (fun h3 => (Nat.le_of_dvd (by omega) h3).trans (by omega)) hs
      nlinarith
    · rw [cube_sub_one_eq] at h2
      exact le_of_prime_dvd (by positivity) h2 (fun h3 => (Nat.le_of_dvd (by omega) h3).trans
        ((Nat.sub_le q 1).trans ((Nat.le_add_left q (q ^ 2)).trans (Nat.le_succ _)))) hs
  have hq2 : q = 2 := by
    by_contra hq2
    have h2 := psl_mono hsle
    have h3 : (q ^ 2 + q + 1) * ((q ^ 2 + q + 1) ^ 2 - 1) <
        2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
      have e1 : (r + 3) ^ 2 - 1 = r ^ 2 + 6 * r + 8 := by
        apply Nat.sub_eq_of_eq_add
        ring
      have e2 : (r + 3) ^ 3 - 1 = r ^ 3 + 9 * r ^ 2 + 27 * r + 26 := by
        apply Nat.sub_eq_of_eq_add
        ring
      rw [e1, e2]
      refine lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) ?_
      ring_nf
      linarith [Nat.zero_le (r ^ 2), Nat.zero_le (r ^ 3), Nat.zero_le (r ^ 4), Nat.zero_le (r ^ 5),
        Nat.zero_le (r ^ 6), Nat.zero_le (r ^ 7), Nat.zero_le (r ^ 8)]
    omega
  subst hq2
  exact ⟨rfl, psl_eq_of_eq (a := 7) (h.trans (by norm_num)) (by norm_num)⟩

theorem psl2_ne_sp4 (hs : s.Prime) (hs5 : 5 ≤ s) {q : ℕ} (hq : 2 ≤ q) (hsq : ¬ s ∣ q) :
    s * (s ^ 2 - 1) ≠ 2 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) := by
  intro h
  have hsq4 : ¬ s ∣ q ^ 4 := fun h3 => hsq (hs.dvd_of_dvd_pow h3)
  have hdvd : s ∣ 2 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) := ⟨s ^ 2 - 1, h.symm⟩
  have h1 := prime_dvd_of_dvd_two_mul hs hs5 hsq4 hdvd
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  have h3 : s ∣ q ^ 2 - 1 → s ≤ q ^ 2 + 1 := fun h3 =>
    (Nat.le_of_dvd (by omega) h3).trans (by omega)
  have hsle : s ≤ q ^ 2 + 1 := by
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · exact h3 h2
    · rw [fourth_sub_one_eq] at h2
      exact le_of_prime_dvd (by positivity) h2 h3 hs
  have h2 := psl_mono hsle
  have h4 : (q ^ 2 + 1) * ((q ^ 2 + 1) ^ 2 - 1) < 2 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
    have e1 : (r + 2) ^ 2 - 1 = r ^ 2 + 4 * r + 3 := by
      apply Nat.sub_eq_of_eq_add
      ring
    have e2 : (r + 2) ^ 4 - 1 = (r ^ 2 + 4 * r + 3) * ((r + 2) ^ 2 + 1) := by
      rw [fourth_sub_one_eq, e1]
    rw [e1, e2]
    refine lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) ?_
    ring_nf
    linarith [Nat.zero_le (r ^ 2), Nat.zero_le (r ^ 3), Nat.zero_le (r ^ 4), Nat.zero_le (r ^ 5),
      Nat.zero_le (r ^ 6), Nat.zero_le (r ^ 7), Nat.zero_le (r ^ 8), Nat.zero_le (r ^ 9),
      Nat.zero_le (r ^ 10)]
  omega

theorem psl2_ne_g2 (hs : s.Prime) (hs5 : 5 ≤ s) {q : ℕ} (hq : 2 ≤ q) (hsq : ¬ s ∣ q) :
    s * (s ^ 2 - 1) ≠ 2 * (q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1))) := by
  intro h
  have hsq6 : ¬ s ∣ q ^ 6 := fun h3 => hsq (hs.dvd_of_dvd_pow h3)
  have hdvd : s ∣ 2 * (q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1))) := ⟨s ^ 2 - 1, h.symm⟩
  have h1 := prime_dvd_of_dvd_two_mul hs hs5 hsq6 hdvd
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  have h3' : s ∣ q ^ 2 - 1 → s ≤ q ^ 4 + q ^ 2 + 1 := fun h3 =>
    (Nat.le_of_dvd (by omega) h3).trans (by omega)
  have hsle : s ≤ q ^ 4 + q ^ 2 + 1 := by
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · rw [sixth_sub_one_eq] at h2
      exact le_of_prime_dvd (by positivity) h2 h3' hs
    · exact h3' h2
  have h2 := psl_mono hsle
  have h4 : (q ^ 4 + q ^ 2 + 1) * ((q ^ 4 + q ^ 2 + 1) ^ 2 - 1) <
      2 * (q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1))) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
    have e1 : (r + 2) ^ 2 - 1 = r ^ 2 + 4 * r + 3 := by
      apply Nat.sub_eq_of_eq_add
      ring
    have e2 : (r + 2) ^ 6 - 1 = (r ^ 2 + 4 * r + 3) * ((r + 2) ^ 4 + (r + 2) ^ 2 + 1) := by
      rw [sixth_sub_one_eq, e1]
    rw [e1, e2]
    refine lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) ?_
    ring_nf
    linarith [Nat.zero_le (r ^ 2), Nat.zero_le (r ^ 3), Nat.zero_le (r ^ 4), Nat.zero_le (r ^ 5),
      Nat.zero_le (r ^ 6), Nat.zero_le (r ^ 7), Nat.zero_le (r ^ 8), Nat.zero_le (r ^ 9),
      Nat.zero_le (r ^ 10), Nat.zero_le (r ^ 11), Nat.zero_le (r ^ 12), Nat.zero_le (r ^ 13),
      Nat.zero_le (r ^ 14)]
  omega

theorem psl_ne_720 (hs : s.Prime) : s * (s ^ 2 - 1) ≠ 720 := by
  intro h
  have h9 : s = 9 := psl_eq_of_eq (a := 9) (h.trans (by norm_num)) (by norm_num)
  rw [h9] at hs
  norm_num at hs

end Arith

section Excl

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {U Z : Subgroup V} {s : ℕ}

theorem two_le_two_pow_of_field {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    2 ≤ 2 ^ n := by
  rw [← hF]
  exact Finite.one_lt_card

theorem binaryNaturalSL_two_two (hs : s.Prime) (hs5 : 5 ≤ s)
    (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K) {n : ℕ} (h : BinaryNaturalSL K U Z 2 n) :
    BinaryNaturalSL K U Z 2 2 := by
  obtain ⟨F, hF1, hF2, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [card_statedSL_two1527d, hF] at h1
  rw [h1] at hK
  obtain ⟨h4, -⟩ := psl2_eq_sl2 hs hs5 (two_le_two_pow_of_field hF) (not_dvd_two_pow hs hs5 n) hK
  exact ⟨F, hF1, hF2, by rw [hF, h4]; norm_num, π, hπ⟩

theorem binaryNaturalSL_three_one' (hs : s.Prime) (hs5 : 5 ≤ s)
    (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K) {n : ℕ} (h : BinaryNaturalSL K U Z 3 n) :
    BinaryNaturalSL K U Z 3 1 := by
  obtain ⟨F, hF1, hF2, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [card_statedSL_three1527d, hF] at h1
  rw [h1] at hK
  obtain ⟨h2, -⟩ := psl2_eq_sl3 hs hs5 (two_le_two_pow_of_field hF) (not_dvd_two_pow hs hs5 n) hK
  exact ⟨F, hF1, hF2, by rw [hF, h2]; norm_num, π, hπ⟩

theorem not_sp4_psl2 (hs : s.Prime) (hs5 : 5 ≤ s) (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K)
    {n : ℕ} (h : BinaryNaturalSp4 K U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF] at h1
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h1
  rw [h1] at hK
  apply psl2_ne_sp4 hs hs5 (two_le_two_pow_of_field hF) (not_dvd_two_pow hs hs5 n)
  rw [hK]
  norm_num

theorem not_g2_psl2 (hs : s.Prime) (hs5 : 5 ≤ s) (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K)
    {n : ℕ} (h : G2Natural K U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcard : Nat.card ↥K = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    have := FFC.charP_two_of_card_pow hF
    exact (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
  rw [card_quasithinG2_1527d hF, hF] at hcard
  rw [hcard] at hK
  exact psl2_ne_g2 hs hs5 (two_le_two_pow_of_field hF) (not_dvd_two_pow hs hs5 n) hK

theorem not_g2d_psl2
    (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K) (h : G2NaturalDerived K U Z 1) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcP := FFC.charP_two_of_card_pow hF
  have hΓ : ⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ≤ CFSG.Open.quasithinG2 F := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (CFSG.Open.quasithinG2 F).mul_mem
      ((CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem ha hb)
        ((CFSG.Open.quasithinG2 F).inv_mem ha)) ((CFSG.Open.quasithinG2 F).inv_mem hb)
  have hcard : Nat.card ↥K = Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
    (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ hΓ) hπ, hπ.1⟩)).symm
  rw [S1549D.card_commutator_quasithinG2_two (by simpa using hF)] at hcard
  rw [hcard] at hK
  exact psl_ne_of_between (a := 22) (by norm_num) (by norm_num) hK

theorem card_eq_of_alternatingNatural {m : ℕ} (hm : 5 ≤ m) (h : AlternatingNatural K U Z m) :
    Nat.card ↥K = m.factorial / 2 := by
  obtain ⟨π, hπ⟩ := h
  have hcard : Nat.card ↥K = Nat.card ↥(alternatingGroup (Fin m)) :=
    (Nat.card_congr (FFC.equivOfRealizes (FFC.altDn_faithful hm) hπ).toEquiv).symm
  rw [hcard, card_alternatingGroup1527d m (by omega)]

theorem not_alt6_psl2 (hs : s.Prime) (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K)
    (h : AlternatingNatural K U Z 6) : False := by
  rw [card_eq_of_alternatingNatural (by norm_num) h] at hK
  exact psl_ne_720 hs (by rw [hK]; norm_num [Nat.factorial])

theorem not_alt7_psl2 (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K)
    (h : AlternatingNatural K U Z 7) : False := by
  rw [card_eq_of_alternatingNatural (by norm_num) h] at hK
  exact psl_ne_of_between (a := 17) (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) hK

theorem not_alt8_psl2 (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K)
    (h : AlternatingNatural K U Z 8) : False := by
  rw [card_eq_of_alternatingNatural (by norm_num) h] at hK
  exact psl_ne_of_between (a := 34) (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) hK

theorem not_a7Four_psl2 (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K) (h : A7Four K U Z) : False := by
  obtain ⟨α, π, hπ⟩ := h
  have hcard : Nat.card ↥K = Nat.card ↥(alternatingGroup (Fin 7)) :=
    (Nat.card_congr (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ).toEquiv).symm
  rw [card_alternatingGroup1527d 7 (by norm_num)] at hcard
  rw [hcard] at hK
  exact psl_ne_of_between (a := 17) (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) hK

theorem not_tripleA6_psl2 (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K) (h : TripleA6Six K U Z) :
    False := by
  obtain ⟨F, _, _, Γ₀, hF, -, hhat, -, π, hπ⟩ := h
  have hcard : Nat.card ↥K = Nat.card ↥Γ₀ :=
    (Nat.card_congr (FFC.equivOfRealizes (FFModel.nat_faithful Γ₀) hπ).toEquiv).symm
  have h2 : Nat.card ↥Γ₀ = 1080 :=
    card_of_isHat1527d hhat (by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial])
  rw [hcard, h2] at hK
  exact psl_ne_of_between (a := 12) (by norm_num) (by norm_num) hK

theorem not_sl_two_psl2 (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K) {d : ℕ} (hd : d = 4 ∨ d = 5)
    {π : ↥(StatedSL d (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL d (ZMod 2))).RealizesVia K U Z π) : False := by
  have h1 := card_eq_of_nat_realizes1527d hπ
  rcases hd with rfl | rfl
  · rw [card_statedSL_four_zmod1527d] at h1
    rw [h1] at hK
    exact psl_ne_of_between (a := 34) (by norm_num) (by norm_num) hK
  · rw [card_statedSL_five_zmod1527d] at h1
    rw [h1] at hK
    exact psl_ne_of_between (a := 271) (by norm_num) (by norm_num) hK

theorem not_extSq_psl2 (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (h : SLExteriorTwo K U Z d) : False := by
  obtain ⟨π, hπ⟩ := h
  have hcard : Nat.card ↥K = Nat.card ↥(StatedSL d (ZMod 2)) :=
    (Nat.card_congr (FFC.equivOfRealizes (FFC.extSq_faithful (by omega)) hπ).toEquiv).symm
  rcases hd with rfl | rfl
  · rw [card_statedSL_four_zmod1527d] at hcard
    rw [hcard] at hK
    exact psl_ne_of_between (a := 34) (by norm_num) (by norm_num) hK
  · rw [card_statedSL_five_zmod1527d] at hcard
    rw [hcard] at hK
    exact psl_ne_of_between (a := 271) (by norm_num) (by norm_num) hK

end Excl

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem psl2_module_of_b51Conclusion
    {H K : Subgroup (MulAut V)} (hB : B51Conclusion H K) {s : ℕ} (hs : s.Prime) (hs5 : 5 ≤ s)
    (hK : s * (s ^ 2 - 1) = 2 * Nat.card ↥K) :
    BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 2 2 ∨
      (fixV K ⊓ commV K = ⊥ ∧ AlternatingNatural K (commV K) ⊥ 5) ∨
      BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 3 1 ∨
      (∃ (I : Fin 2 → Subgroup V) (π : ↥(StatedSL 3 (ZMod 2)) →* ↥K), iSupIndep I ∧
        (⨆ i, I i) = commV K ∧
          ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K (I i) ⊥ π) := by
  obtain ⟨hp1, hp2, -⟩ := hB
  by_cases hZ : fixV K ⊓ commV K = ⊥
  · rcases hp1.2 with hi | hii | ⟨n, hiii⟩ | hiv
    · rcases hi.2.1 with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl (binaryNaturalSL_two_two hs hs5 hK h)
      · exact Or.inr (Or.inr (Or.inl (binaryNaturalSL_three_one' hs hs5 hK h)))
      · exact (not_sp4_psl2 hs hs5 hK h).elim
      · exact (not_g2_psl2 hs hs5 hK h).elim
      · exact (not_g2d_psl2 hK h).elim
      · refine Or.inr (Or.inl ⟨hZ, ?_⟩)
        rw [hZ] at h
        exact h
      · exact (not_alt6_psl2 hs hK h).elim
      · exact (not_alt7_psl2 hK h).elim
      · exact (not_a7Four_psl2 hK h).elim
      · exact (not_tripleA6_psl2 hK h).elim
      · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
        exact (not_sl_two_psl2 hK (Or.inl rfl) hπ).elim
      · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
        exact (not_sl_two_psl2 hK (Or.inr rfl) hπ).elim
      · exact (not_extSq_psl2 hK (Or.inl rfl) h).elim
      · exact (not_extSq_psl2 hK (Or.inr rfl) h).elim
    · obtain ⟨-, n, F, _, _, hF, I, π, hind, hsup, hreal, -⟩ := hii
      have h1 := card_eq_of_nat_realizes1527d (hreal 0)
      rw [card_statedSL_three1527d, hF] at h1
      rw [h1] at hK
      obtain ⟨h2, -⟩ :=
        psl2_eq_sl3 hs hs5 (two_le_two_pow_of_field hF) (not_dvd_two_pow hs hs5 n) hK
      have hF2 : Nat.card F = 2 := by rw [hF, h2]
      exact Or.inr (Or.inr (Or.inr ⟨I, π.comp (FFC.slOfZMod (FFC.ringEquivZModTwo F hF2) 3), hind,
        hsup, fun i => FFC.realizesVia_zmod hF2 (hreal i)⟩))
    · exfalso
      obtain ⟨hn, π, U₁, U₂, -, hreal, -⟩ := hiii.2
      exact not_sl_two_psl2 hK hn hreal
    · exfalso
      obtain ⟨-, n, hn, k, hk, -, hdir⟩ := hiv
      obtain ⟨I, π, -, -, -, hreal⟩ := hdir
      exact not_sl_two_psl2 hK hn (hreal ⟨0, hk⟩)
  · have hnot : ¬ IsIntDirect (commV K) (fixV K) ⊤ := fun hd => hZ (by
      have := hd.2
      rwa [inf_comm] at this)
    obtain ⟨-, hl⟩ := hp2.2 hnot
    rcases hl with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h
    · exact Or.inl (binaryNaturalSL_two_two hs hs5 hK h)
    · exact (not_sp4_psl2 hs hs5 hK h).elim
    · exact (not_g2_psl2 hs hs5 hK h).elim
    · exact (not_alt6_psl2 hs hK h).elim
    · exact (not_alt8_psl2 hK h).elim
    · exact (not_g2d_psl2 hK h).elim
    · exact Or.inr (Or.inr (Or.inl h))

end Main

end CFSG.Quasithin.H13.NQRigid
