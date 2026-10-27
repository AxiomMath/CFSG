module

public import CFSG.Quasithin.Vol2.Ch11SecO7j
public import CFSG.Quasithin.Vol2.Ch11SecO7c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem le_of_prime_dvd_mul {r a b M : ℕ} (hr : r.Prime) (h : r ∣ a * b) (ha : r ∣ a → r ≤ M)
    (hb : r ∣ b → r ≤ M) : r ≤ M := by
  rcases hr.dvd_mul.mp h with h | h
  · exact ha h
  · exact hb h

theorem psl2_ne_rank2 {p r N c X : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hr : r.Prime) (hr2 : r ≠ 2)
    (hN : N * 2 = r * (r ^ 2 - 1)) (hc : c ∣ 3)
    (hX : X = (p ^ 2 - 1) * (p ^ 3 - 1) ∨ X = (p ^ 2 - 1) * (p ^ 3 + 1))
    (h : p ^ 3 * X = N * c) : False := by
  have hc3 : c ≤ 3 := Nat.le_of_dvd (by norm_num) hc
  have hcp : Nat.Coprime p c := Nat.Coprime.coprime_dvd_right hc
    ((Nat.coprime_primes hp Nat.prime_three).mpr (by omega))
  have hrN : r ∣ N := by
    have h1 : r ∣ N * 2 := hN ▸ dvd_mul_right r _
    exact Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_primes hr Nat.prime_two).mpr hr2) h1
  have hrX : r ∣ p ^ 3 * X := h ▸ hrN.mul_right c
  have h1p : 1 ≤ p := by omega
  have hp2 : 49 ≤ p ^ 2 := by nlinarith
  rcases hr.dvd_mul.mp hrX with h1 | h1
  ·
    have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h1)
    subst hrp
    have h3 : r ^ 3 ∣ N := (Nat.Coprime.pow_left 3 hcp).dvd_of_dvd_mul_right
      (h ▸ dvd_mul_right _ _)
    have h4 : r * r ^ 2 ∣ r * (r ^ 2 - 1) := by
      rw [← hN, show r * r ^ 2 = r ^ 3 by ring]
      exact h3.mul_right 2
    have h5 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mul_dvd_mul_left hr.pos h4)
    omega
  ·
    have e2 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      zify [h1p, Nat.one_le_pow 2 p (by omega)]
      ring
    have e3m : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
      zify [h1p, Nat.one_le_pow 3 p (by omega)]
      ring
    have e3p : p ^ 3 + 1 = (p + 1) * (p * (p - 1) + 1) := by
      zify [h1p]
      ring
    have hpp : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
    have hb1 : p - 1 ≤ 2 * p ^ 2 := by omega
    have hb2 : p + 1 ≤ 2 * p ^ 2 := by omega
    have hb3 : p ^ 2 + p + 1 ≤ 2 * p ^ 2 := by nlinarith
    have hb4 : p * (p - 1) + 1 ≤ 2 * p ^ 2 := by
      have : p * (p - 1) ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left p (Nat.sub_le p 1)
      omega
    have hf : ∀ f, 0 < f → f ≤ 2 * p ^ 2 → r ∣ f → r ≤ 2 * p ^ 2 :=
      fun f hf hfM hrf => (Nat.le_of_dvd hf hrf).trans hfM
    have hrle : r ≤ 2 * p ^ 2 := by
      rcases hX with rfl | rfl
      · rw [e2, e3m] at h1
        exact le_of_prime_dvd_mul hr h1
          (fun h => le_of_prime_dvd_mul hr h (hf _ (by omega) hb1) (hf _ (by omega) hb2))
          (fun h => le_of_prime_dvd_mul hr h (hf _ (by omega) hb1) (hf _ (by omega) hb3))
      · rw [e2, e3p] at h1
        exact le_of_prime_dvd_mul hr h1
          (fun h => le_of_prime_dvd_mul hr h (hf _ (by omega) hb1) (hf _ (by omega) hb2))
          (fun h => le_of_prime_dvd_mul hr h (hf _ (by omega) hb2) (hf _ (by omega) hb4))
    have hA : N * 2 ≤ 8 * p ^ 6 := by
      rw [hN]
      calc r * (r ^ 2 - 1) ≤ r * r ^ 2 := Nat.mul_le_mul_left r (Nat.sub_le _ _)
        _ = r ^ 3 := by ring
        _ ≤ (2 * p ^ 2) ^ 3 := Nat.pow_le_pow_left hrle 3
        _ = 8 * p ^ 6 := by ring
    have hX1 : 6 * p ≤ p ^ 2 - 1 := by
      have : 7 * p ≤ p ^ 2 := by nlinarith
      omega
    have hX2 : 6 * p ^ 2 ≤ p ^ 3 - 1 := by
      have : 7 * p ^ 2 ≤ p ^ 3 := by
        rw [show p ^ 3 = p * p ^ 2 by ring]
        exact Nat.mul_le_mul_right _ hp7
      omega
    have hX36 : 36 * p ^ 3 ≤ X := by
      have h6 : 36 * p ^ 3 = (6 * p) * (6 * p ^ 2) := by ring
      rcases hX with rfl | rfl
      · rw [h6]
        exact Nat.mul_le_mul hX1 hX2
      · rw [h6]
        exact Nat.mul_le_mul hX1 (hX2.trans (by omega))
    have hB : 36 * p ^ 6 ≤ N * 3 := by
      calc 36 * p ^ 6 = p ^ 3 * (36 * p ^ 3) := by ring
        _ ≤ p ^ 3 * X := Nat.mul_le_mul_left _ hX36
        _ = N * c := h
        _ ≤ N * 3 := Nat.mul_le_mul_left N hc3
    have hp6 : 0 < p ^ 6 := by positivity
    omega

theorem card_mul_two_of_psl2 {L : Type} [Group L] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : IsPSL 2 r 1 L) : Nat.card L * 2 = r * (r ^ 2 - 1) := by
  have hc := H13.NotLie.card_psl2 h
  have hg : Nat.gcd 2 (r ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact Nat.gcd_eq_left ((Nat.Prime.even_sub_one hr hr2).two_dvd)
  rw [hg, pow_one] at hc
  have hev : 2 ∣ r * (r ^ 2 - 1) :=
    Dvd.dvd.mul_left (even_iff_two_dvd.mp
      (Nat.Odd.sub_odd ((hr.odd_of_ne_two hr2).pow) odd_one)) r
  rw [hc, Nat.div_mul_cancel hev]

theorem prime_dvd_card_psl2 {L : Type} [Group L] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : IsPSL 2 r 1 L) : r ∣ Nat.card L := by
  have h1 : r ∣ Nat.card L * 2 := card_mul_two_of_psl2 hr hr2 h ▸ dvd_mul_right r _
  exact Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_primes hr Nat.prime_two).mpr hr2) h1

theorem not_T_of_psl2 {L : Type} [Group L] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : IsPSL 2 r 1 L) : ∀ p, p.Prime → 7 ≤ p → ¬ InT p L := by
  intro p hp hp7 hT
  have hN := card_mul_two_of_psl2 hr hr2 h
  rcases card_T hp hp7 hT with h1 | h1 | h1 | h1 | h1
  · have hrp : r = p ^ 2 :=
      eq_of_cube_sub hr.one_lt.le (Nat.one_le_pow _ _ hp.pos) (hN.symm.trans h1.symm)
    exact Nat.Prime.not_prime_pow le_rfl (hrp ▸ hr)
  · exact psl2_ne_rank2 hp hp7 hr hr2 hN (Nat.gcd_dvd_left 3 _) (Or.inl rfl) h1
  · exact psl2_ne_rank2 hp hp7 hr hr2 hN (one_dvd 3) (Or.inl rfl) (by rw [h1, mul_one])
  · exact psl2_ne_rank2 hp hp7 hr hr2 hN (Nat.gcd_dvd_left 3 _) (Or.inr rfl) h1
  · exact psl2_ne_rank2 hp hp7 hr hr2 hN (one_dvd 3) (Or.inr rfl) (by rw [h1, mul_one])

theorem card_of_sl2_four {B : Type} [Group B] [Finite B] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {φ : B →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hφ : Function.Surjective φ) (hk : IsPGroup 2 ↥φ.ker) : ∃ a, Nat.card B = 2 ^ a * 15 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  have h1 : Nat.card B = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * Nat.card φ.ker := by
    rw [φ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF, hk] at h1
  refine ⟨k + 2, ?_⟩
  rw [h1, pow_add]
  norm_num
  ring

theorem card_modO2_of {Y : Type} [Group Y] {B : Subgroup Y} [Finite ↥B] {a : ℕ}
    (hB : Nat.card ↥B = 2 ^ a * 15) : ∃ c, Nat.card (ModO2 B) = 2 ^ c * 15 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
  have h1 : Nat.card ↥B = Nat.card (ModO2 B) * 2 ^ b := by
    rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, hb]
  have hM0 : Nat.card (ModO2 B) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    have : 0 < 2 ^ a * 15 := by positivity
    omega
  obtain ⟨c, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd hM0
  have h2 : 2 ^ (c + b) * m = 2 ^ a * 15 := by rw [← hB, h1, hcm, pow_add]; ring
  have h3 := SecA.eq_of_two_pow_mul_odd hm ⟨7, rfl⟩ h2
  rw [h3] at h2
  have hm15 : m = 15 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
  exact ⟨c, by rw [hcm, hm15]⟩

theorem eq_three_or_five {a r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : r ∣ 2 ^ a * 15) :
    r = 3 ∨ r = 5 := by
  have h1 : r ∣ 3 * 5 := (Nat.Coprime.pow_right a
    ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)).dvd_of_dvd_mul_left h
  rcases hr.dvd_mul.mp h1 with h3 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h3)

theorem dvd_fifteen {a d : ℕ} (hd : Odd d) (h : d ∣ 2 ^ a * 15) : d ∣ 15 :=
  (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hd)).dvd_of_dvd_mul_left h

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
