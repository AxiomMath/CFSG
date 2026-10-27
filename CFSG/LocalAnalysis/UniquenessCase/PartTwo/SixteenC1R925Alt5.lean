module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925L2
public import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
public import CFSG.Goldschmidt.J1ModelTransport
public import CFSG.LocalAnalysis.OddStandard.L2Ree.SporadicJ3
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

private lemma r925_ordA_one_eq (q : ℕ) :
    CFSG.Open.ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
  norm_num [CFSG.Open.ordA, Finset.Icc_self]

private lemma r925_ordA_two_eq (q : ℕ) :
    CFSG.Open.ordA 2 q =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  unfold CFSG.Open.ordA
  rw [show Finset.Icc 2 (2 + 1) = {2, 3} by rfl, Finset.prod_pair (by norm_num)]

theorem r925_alt5_of_psl2_dvd
    {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hX : LieModel X .PSL 2 p f) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1)
    (hd : Nat.card X ∣ 51840) : IsAlt X 5 := by
  have hp : Nat.Prime p := hX.admissible.1
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hqne2 : p ^ f ≠ 2 := fun h2 => hX.admissible.2.2.2.1 (by rw [h2])
  have hqne3 : p ^ f ≠ 3 := fun h3 => hX.admissible.2.2.2.2 (by rw [h3])
  have hcard := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hX
  rw [hcard] at hd
  generalize hq : p ^ f = q at hd ⊢
  have hq2 : 2 ≤ q := by
    have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hq45 : 4 ≤ q := by
    have hqne2' : q ≠ 2 := fun h2 => hqne2 (by rw [hq, h2])
    have hqne3' : q ≠ 3 := fun h3 => hqne3 (by rw [hq, h3])
    omega
  have hg_dvd : Nat.gcd 2 (q - 1) ∣ q * (q ^ 2 - 1) := by
    have h2 : q - 1 ∣ q ^ 2 - 1 := by
      refine ⟨q + 1, ?_⟩
      show q ^ 2 - 1 ^ 2 = (q - 1) * (q + 1)
      rw [Nat.pow_two_sub_pow_two, Nat.mul_comm]
    exact (Nat.gcd_dvd_right 2 (q - 1)).trans (h2.trans (dvd_mul_left _ _))
  have hmul : q * (q ^ 2 - 1) = CFSG.Open.ordA 1 q * Nat.gcd 2 (q - 1) := by
    rw [r925_ordA_one_eq]
    exact (Nat.div_mul_cancel hg_dvd).symm
  have hle : CFSG.Open.ordA 1 q ≤ 51840 := Nat.le_of_dvd (by norm_num) hd
  have hgle : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left (q - 1) (by norm_num)
  have hprod : q * (q ^ 2 - 1) ≤ 103680 := by
    rw [hmul]
    nlinarith
  have hq46 : q ≤ 46 := by
    by_contra hcon
    have hq47 : 47 ≤ q := by have h := not_le.1 hcon; omega
    have h2 : (47 : ℕ) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq47 2
    have h1 : 47 * (47 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq47 (by omega)
    norm_num at h1
    omega
  have hq_cases : q = 4 ∨ q = 5 ∨ q = 9 := by
    rw [r925_ordA_one_eq] at hd
    interval_cases q <;> first | decide | (exfalso; norm_num at hd)
  rcases hq_cases with hq4 | hq5 | hq9
  · have hc : Nat.card X = 60 := by
      rw [hcard, hq, hq4]
      norm_num [r925_ordA_one_eq]
    exact CFSG.OddStandard.L2Ree.nonempty_mulEquiv_alternatingGroup_five_of_lieModel_card_sixty
      hp hX hc
  · have hc : Nat.card X = 60 := by
      rw [hcard, hq, hq5]
      norm_num [r925_ordA_one_eq]
    exact CFSG.OddStandard.L2Ree.nonempty_mulEquiv_alternatingGroup_five_of_lieModel_card_sixty
      hp hX hc
  · exfalso
    have hpq : p ^ f = 9 := hq.trans hq9
    have hpdvd : p ∣ 9 := by
      rw [← hpq]
      exact dvd_pow_self p (n := f) (by omega)
    have hp3 : p = 3 := by
      have h9 : p ∣ 3 ^ 2 := by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hpdvd
        exact hpdvd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h9)
    subst hp3
    have hf2 : f = 2 := Nat.pow_right_injective (a := 3) (by norm_num)
      (hpq.trans (by norm_num))
    subst hf2
    have h2 := two_le_pRank_psl2_three_pow hX
    omega

theorem r925_not_dvd_psl3 {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hX : LieModel X .PSL 3 p f) (h : p ^ f % 3 = 2) : ¬ Nat.card X ∣ 51840 := by
  intro hd
  have hp : Nat.Prime p := hX.admissible.1
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hcard := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hX
  rw [hcard] at hd
  generalize hq : p ^ f = q at h hd ⊢
  have hq2 : 2 ≤ q := by
    have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hgcd : Nat.gcd 3 (q - 1) = 1 := by
    have h3 : ¬ 3 ∣ q - 1 := by
      intro hdvd
      have hmod0 : (q - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
      have hq1 : 1 ≤ q := by omega
      have hqeq : q = (q - 1) + 1 := (Nat.sub_add_cancel hq1).symm
      have hmod : q % 3 = 1 := by rw [hqeq, Nat.add_mod, hmod0]
      omega
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q - 1)) with h1 | h3'
    · exact h1
    · exact absurd (h3' ▸ Nat.gcd_dvd_right 3 (q - 1)) h3
  have hord : CFSG.Open.ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [r925_ordA_two_eq, hgcd, Nat.div_one]
  rw [hord] at hd
  have hle : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 51840 :=
    Nat.le_of_dvd (by norm_num) hd
  have hq4 : q ≤ 4 := by
    by_contra hcon
    have hq5 : 5 ≤ q := by have h := not_le.1 hcon; omega
    have h1 : (5 : ℕ) ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
    have h2 : (5 : ℕ) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
    have h1' : 125 ≤ q ^ 3 := by norm_num at h1; exact h1
    have h2' : 24 ≤ q ^ 2 - 1 := by norm_num at h2; omega
    have h3' : 124 ≤ q ^ 3 - 1 := by omega
    have hge : 125 * (24 * 124) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h1' (Nat.mul_le_mul h2' h3')
    omega
  interval_cases q
  · exact absurd hd (by norm_num)
  · norm_num at h
  · norm_num at h

theorem r925_not_dvd_psu3 {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hX : LieModel X .PSU 3 p f) (h : p ^ f % 3 = 1) : ¬ Nat.card X ∣ 51840 := by
  intro hd
  have hp : Nat.Prime p := hX.admissible.1
  have hf1 : 1 ≤ f := hX.admissible.2.1
  obtain ⟨-, K, hFld, hFin, hKcard, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have hord0 : Nat.card X * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd
      (p := p) (f := f) hp hf1 hKcard
  generalize hq : p ^ f = q at h hd hord0 ⊢
  have hq2 : 2 ≤ q := by
    have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hq4 : 4 ≤ q := by
    have hne2 : q ≠ 2 := by intro h2; rw [h2] at h; norm_num at h
    have hne3 : q ≠ 3 := by intro h3; rw [h3] at h; norm_num at h
    omega
  have hgcd : Nat.gcd 3 (q + 1) = 1 := by
    have h3 : ¬ 3 ∣ q + 1 := by
      intro hdvd
      have hmod0 : (q + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
      have hmod : (q + 1) % 3 = 2 := by rw [Nat.add_mod, h]
      omega
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q + 1)) with h1 | h3'
    · exact h1
    · exact absurd (h3' ▸ Nat.gcd_dvd_right 3 (q + 1)) h3
  have hord : Nat.card X = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rw [hgcd, Nat.mul_one] at hord0
    exact hord0
  rw [hord] at hd
  have hle : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ≤ 51840 :=
    Nat.le_of_dvd (by norm_num) hd
  have h1 : (4 : ℕ) ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
  have h2 : (4 : ℕ) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
  have h1' : 64 ≤ q ^ 3 := by norm_num at h1; exact h1
  have h2' : 15 ≤ q ^ 2 - 1 := by norm_num at h2; omega
  have h3' : 65 ≤ q ^ 3 + 1 := by omega
  have hge : 62400 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Nat.mul_le_mul h1' (Nat.mul_le_mul h2' h3')
  omega

theorem r925_not_dvd_j1 {X : Type} [Group X] [Finite X] (hX : IsSpor X .J1) :
    ¬ Nat.card X ∣ 51840 := by
  intro hd
  have hcard : Nat.card X = 175560 := by
    obtain ⟨e⟩ := CFSG.Open.goldschmidtJ1_iso_iff_native.mpr hX
    rw [Nat.card_congr e.toEquiv]
    rw [show CFSG.Open.goldschmidtJ1 = CFSG.Open.walterJ1 from rfl]
    exact CFSG.Walter.J1Props.card_walterJ1
  rw [hcard] at hd
  have := Nat.le_of_dvd (by norm_num : 0 < 51840) hd
  omega

theorem r925_alt5_of_dvd
    (hK32 : UCK.K32) {X : Type} [Group X] [Finite X]
    (hKG : CFSG.Open.IsKGroup X) (hs : IsSimpleGroup X) (hn : ∃ a b : X, a * b ≠ b * a)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1) (hd : Nat.card X ∣ 51840) : IsAlt X 5 := by
  rcases hK32 X hKG hs hn hr with ⟨p, f, h⟩ | ⟨p, f, h3, h⟩ | ⟨p, f, h3, h⟩ | h
  · exact r925_alt5_of_psl2_dvd h hr hd
  · exact absurd hd (r925_not_dvd_psl3 h h3)
  · exact absurd hd (r925_not_dvd_psu3 h h3)
  · exact absurd hd (r925_not_dvd_j1 h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
