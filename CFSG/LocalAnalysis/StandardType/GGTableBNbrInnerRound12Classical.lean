module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMore
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRound12ExcRow
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace Round12Cl

theorem not_two_dvd_sub {n : ℕ} (hn : 1 ≤ n) : ¬ 2 ∣ 2 ^ n - 1 := by
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

theorem not_two_dvd_add {n : ℕ} (hn : 1 ≤ n) : ¬ 2 ∣ 2 ^ n + 1 := by
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  omega

theorem sq_sub_one_eq (n : ℕ) : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by omega⟩
  rw [hm]
  have h2 : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
  simp only [Nat.add_sub_cancel]
  omega

theorem dvd_sub_or_add {p n : ℕ} (hp : p.Prime) (h : p ∣ (2 ^ n) ^ 2 - 1) :
    p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
  rw [sq_sub_one_eq] at h
  exact (Nat.Prime.dvd_mul hp).mp h

theorem dvd_sq_of_dvd_sub {p n : ℕ} (h : p ∣ 2 ^ n - 1) : p ∣ (2 ^ n) ^ 2 - 1 := by
  rw [sq_sub_one_eq]
  exact Dvd.dvd.mul_right h _

theorem ne_two_of_sub {p n : ℕ} (hn : 1 ≤ n) (h : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  exact not_two_dvd_sub hn h

theorem ne_two_of_add {p n : ℕ} (hn : 1 ≤ n) (h : p ∣ 2 ^ n + 1) : p ≠ 2 := by
  rintro rfl
  exact not_two_dvd_add hn h

end Round12Cl

theorem GGTableBNbrInnerRound12Label.parts {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTableBNbrInnerRound12Label p lab) :
    ¬ GGTypeALabel p lab ∧ ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1) ∧
    ¬ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∧
    ¬ GGTableBF4Label p lab ∧ ¬ GGUnitaryCoprimeLabel p lab ∧ ¬ GGSpNonsplitLabel p lab ∧
    ¬ GGTableBNbrInnerExcSplitLabel p lab ∧ ¬ GGTableBNbrInnerVacLabel p lab ∧
    ¬ GGTableBNbrInnerNineSmallLabel p lab ∧ ¬ GGTableBNbrInnerNineClassicalLabel p lab ∧
    ¬ GGTableBNbrInnerTypeADvdLabel p lab ∧ ¬ GGOrthNsLabel p lab ∧ ¬ GGNbrNsVacLabel p lab := by
  obtain ⟨⟨⟨⟨⟨⟨hA, hBC, hD, hF4⟩, hUC, hSp, hExc, hVac⟩, hSmall, hCl⟩, hDvd⟩, hOrth⟩, hNsVac⟩ := h
  exact ⟨hA, hBC, hD, hF4, hUC, hSp, hExc, hVac, hSmall, hCl, hDvd, hOrth, hNsVac⟩

namespace Round12Cl

theorem linear {p l n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hl1 : 1 ≤ l)
    (h : GGTableBNbrInnerRound12Label p ⟨.A, l, n⟩) :
    GGTableBNbrInnerLinearNsLabel p ⟨.A, l, n⟩ := by
  obtain ⟨hTA, -, -, -, -, -, -, hVac, hSmall, hCl, hDvd, -, -⟩ := h.parts
  by_cases hq : p ∣ 2 ^ n - 1
  · have hpl : p ∣ l + 1 := by
      by_contra hpl
      exact hTA (Or.inl ⟨rfl, hq, hpl⟩)
    have hp2 : p ≠ 2 := ne_two_of_sub hn hq
    rcases Nat.lt_or_ge l 4 with hl4 | hl4
    · exfalso
      rcases (show l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl
      · exact hVac (Or.inl (Or.inl ⟨rfl, rfl⟩))
      · exact hSmall (by simp [GGTableBNbrInnerNineSmallLabel])
      · have h4 : p ∣ 2 ^ 2 := by simpa using hpl
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
    · exact absurd ⟨rfl, hl4, hq, hpl⟩ hDvd
  · rcases Nat.lt_or_ge l 4 with hl4 | hl4
    · exfalso
      rcases (show l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl
      · exact hVac (Or.inl (Or.inl ⟨rfl, rfl⟩))
      · exact hSmall (by simp [GGTableBNbrInnerNineSmallLabel])
      · apply hCl
        refine Or.inl ⟨Or.inl ⟨rfl, by norm_num⟩, fun j hj hj3 => ?_⟩
        have hj1 : j = 1 := by simp at hj3; omega
        subst hj1
        simpa using hq
    · have hp2 : p ≠ 2 := by
        rintro rfl
        apply hCl
        refine Or.inl ⟨Or.inl ⟨rfl, (show 2 ≤ l by omega)⟩, fun j hj _ => ?_⟩
        show ¬ 2 ∣ (2 ^ n) ^ j - 1
        have h2 : 2 ∣ (2 ^ n) ^ j := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
        have h1 : 1 ≤ (2 ^ n) ^ j := Nat.one_le_pow _ _ (Nat.one_le_two_pow)
        omega
      exact ⟨rfl, hl4, hp2, hq⟩

theorem twA {p l n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hl : 2 ≤ l)
    (h : GGTableBNbrInnerRound12Label p ⟨.twA, l, n⟩) :
    GGTableBNbrInnerUnitaryHypLabel p ⟨.twA, l, n⟩ ∨ GGUnitDvdLabelNo63 p ⟨.twA, l, n⟩ ∨
      GGUnitDvd63Label p ⟨.twA, l, n⟩ := by
  obtain ⟨-, -, -, -, hUC, -, -, -, hSmall, hCl, -, -, hNsVac⟩ := h.parts
  have hl2 : l ≠ 2 := by
    rintro rfl
    exact hSmall (by simp [GGTableBNbrInnerNineSmallLabel])
  by_cases hq1 : p ∣ 2 ^ n + 1
  · have hpl : p ∣ l + 1 := by
      by_contra hpl
      exact hUC (Or.inl ⟨rfl, hq1, hpl⟩)
    have hl4 : 4 ≤ l := by
      by_contra hlt
      have hl3 : l = 3 := by omega
      subst hl3
      have h4 : p ∣ 2 ^ 2 := by simpa using hpl
      exact ne_two_of_add hn hq1
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
    by_cases h63 : l = 5 ∧ p = 3
    · exact Or.inr (Or.inr ⟨⟨rfl, (show 3 ≤ l by omega), hq1, hpl⟩, h63⟩)
    · exact Or.inr (Or.inl ⟨⟨rfl, (show 3 ≤ l by omega), hq1, hpl⟩, h63⟩)
  · have hcases : l = 3 ∨ (l = 5 ∧ p ∣ 2 ^ n - 1) := by
      by_contra hcon
      push Not at hcon
      exact hNsVac (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (show 4 ≤ l by omega), hq1,
        fun h5 => hcon.2 h5⟩))))
    rcases hcases with rfl | ⟨rfl, hq⟩
    · have hsq : p ∣ (2 ^ n) ^ 2 - 1 := by
        by_contra hsq
        apply hCl
        refine Or.inr (Or.inl ⟨Or.inl ⟨rfl, (show 2 ≤ 3 by omega)⟩, fun j hj hj3 => ?_⟩)
        have hj1 : j = 1 := by simp at hj3; omega
        subst hj1
        simpa using hsq
      rcases dvd_sub_or_add hp hsq with hq | hq
      · exact Or.inl ⟨Or.inl ⟨rfl, Or.inl rfl⟩, ne_two_of_sub hn hq, hq⟩
      · exact absurd hq hq1
    · exact Or.inl ⟨Or.inl ⟨rfl, Or.inr rfl⟩, ne_two_of_sub hn hq, hq⟩

theorem twD {p l n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hl : 2 ≤ l)
    (h : GGTableBNbrInnerRound12Label p ⟨.twD, l, n⟩) :
    GGTableBNbrInnerUnitaryHypLabel p ⟨.twD, l, n⟩ := by
  obtain ⟨-, -, hD, -, hUC, -, -, hVac, -, hCl, -, hOrth, hNsVac⟩ := h.parts
  rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with rfl | rfl | hl4
  · exact absurd (Or.inl (Or.inr ⟨rfl, rfl⟩)) hVac
  · by_cases hq1 : p ∣ 2 ^ n + 1
    · exact absurd (Or.inr ⟨rfl, rfl, hq1⟩) hUC
    · have hsq : p ∣ (2 ^ n) ^ 2 - 1 := by
        by_contra hsq
        apply hCl
        refine Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, fun j hj hj3 => ?_⟩)
        have hj1 : j = 1 := by simp at hj3; omega
        subst hj1
        simpa using hsq
      rcases dvd_sub_or_add hp hsq with hq | hq
      · exact ⟨Or.inr ⟨rfl, rfl⟩, ne_two_of_sub hn hq, hq⟩
      · exact absurd hq hq1
  · exfalso
    by_cases hq : p ∣ 2 ^ n - 1
    · exact hD ⟨Or.inr rfl, hl4, hq⟩
    · by_cases hq1 : p ∣ 2 ^ n + 1
      · exact hOrth ⟨Or.inr rfl, hl4, hq1⟩
      · exact hNsVac (Or.inr (Or.inl ⟨Or.inr rfl, hl4, hq, hq1⟩))

theorem D {p l n : ℕ} (hl : 3 ≤ l) (h : GGTableBNbrInnerRound12Label p ⟨.D, l, n⟩) : False := by
  obtain ⟨hTA, -, hD, -, -, -, -, -, -, hCl, -, hOrth, hNsVac⟩ := h.parts
  rcases (show l = 3 ∨ 4 ≤ l by omega) with rfl | hl4
  · by_cases hq : p ∣ 2 ^ n - 1
    · exact hTA (Or.inr (Or.inl ⟨rfl, rfl, hq⟩))
    · apply hCl
      refine Or.inl ⟨Or.inr ⟨rfl, rfl⟩, fun j hj hj3 => ?_⟩
      have hj1 : j = 1 := by simp at hj3; omega
      subst hj1
      simpa using hq
  · by_cases hq : p ∣ 2 ^ n - 1
    · exact hD ⟨Or.inl rfl, hl4, hq⟩
    · by_cases hq1 : p ∣ 2 ^ n + 1
      · exact hOrth ⟨Or.inl rfl, hl4, hq1⟩
      · exact hNsVac (Or.inr (Or.inl ⟨Or.inl rfl, hl4, hq, hq1⟩))

theorem BC {p l n : ℕ} {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C)
    (h : GGTableBNbrInnerRound12Label p ⟨t, l, n⟩) : False := by
  obtain ⟨-, hBC, -, -, -, hSp, -, -, -, -, -, -, hNsVac⟩ := h.parts
  by_cases hq : p ∣ 2 ^ n - 1
  · exact hBC ⟨ht, hq⟩
  · by_cases hq1 : p ∣ 2 ^ n + 1
    · exact hSp ⟨ht, hq1⟩
    · exact hNsVac (Or.inl ⟨ht, hq, hq1⟩)

theorem small {p l n : ℕ} {t : LargeEvenLieTag}
    (ht : t = .G2 ∨ t = .G2der ∨ t = .twF4der ∨ t = .B2der ∨ t = .twB2 ∨ t = .triD4)
    (h : GGTableBNbrInnerRound12Label p ⟨t, l, n⟩) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, hSmall, -, -, -, hNsVac⟩ := h.parts
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hSmall (Or.inl rfl)
  · exact hSmall (Or.inr (Or.inl rfl))
  · exact hSmall (Or.inr (Or.inr (Or.inl rfl)))
  · exact hSmall (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact hSmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · by_cases hp3 : p = 3
    · exact hSmall (by simp [GGTableBNbrInnerNineSmallLabel, hp3])
    · by_cases hsq : p ∣ (2 ^ n) ^ 2 - 1
      · exact hSmall (by simp [GGTableBNbrInnerNineSmallLabel, hsq])
      · have hq : ¬ p ∣ 2 ^ n - 1 := fun hq => hsq (dvd_sq_of_dvd_sub hq)
        exact hNsVac (by simp [GGNbrNsVacLabel, GGNbrNsTriD4Label, hq, hp3])

theorem excF4 {p l n : ℕ} (h : GGTableBNbrInnerRound12Label p ⟨.F4, l, n⟩) : p ∣ 2 ^ n + 1 := by
  obtain ⟨-, -, -, hF4, -, -, -, -, -, -, -, -, hNsVac⟩ := h.parts
  by_contra hq1
  by_cases hq : p ∣ 2 ^ n - 1
  · exact hF4 ⟨rfl, hq⟩
  · exact hNsVac (by simp [GGNbrNsVacLabel, GGNbrNsF4Label, hq, hq1])

theorem excE78 {p l n : ℕ} {t : LargeEvenLieTag} (ht : t = .E7 ∨ t = .E8)
    (h : GGTableBNbrInnerRound12Label p ⟨t, l, n⟩) : p ∣ 2 ^ n + 1 := by
  obtain ⟨-, -, -, -, -, -, hExc, -, -, -, -, -, hNsVac⟩ := h.parts
  by_contra hq1
  by_cases hq : p ∣ 2 ^ n - 1
  · exact hExc ⟨Or.inr ht, hq⟩
  · rcases ht with rfl | rfl
    · exact hNsVac (by simp [GGNbrNsVacLabel, GGNbrNsE7Label, hq, hq1])
    · exact hNsVac (by simp [GGNbrNsVacLabel, GGNbrNsE8Label, hq, hq1])

theorem excE6 {p l n : ℕ} (h : GGTableBNbrInnerRound12Label p ⟨.E6, l, n⟩) :
    (p = 3 ∧ p ∣ 2 ^ n - 1) ∨ (n = 1 ∧ (p = 3 ∨ p = 7)) := by
  obtain ⟨-, -, -, -, -, -, hExc, -, -, -, -, -, hNsVac⟩ := h.parts
  by_cases hq : p ∣ 2 ^ n - 1
  · left
    refine ⟨?_, hq⟩
    by_contra hp3
    exact hExc ⟨Or.inl ⟨rfl, hp3⟩, hq⟩
  · right
    by_contra hcon
    push Not at hcon
    exact hNsVac (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hq,
      fun ⟨h1, h3⟩ => (hcon h1).1 h3, fun ⟨h1, h7⟩ => (hcon h1).2 h7⟩))))))

theorem excTwE6 {p l n : ℕ} (h : GGTableBNbrInnerRound12Label p ⟨.twE6, l, n⟩) :
    p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hNsVac⟩ := h.parts
  by_contra hcon
  push Not at hcon
  exact hNsVac (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, hcon.1, hcon.2⟩)))))))

theorem excTwF4 {p l n : ℕ} (h : GGTableBNbrInnerRound12Label p ⟨.twF4, l, n⟩) :
    p ∣ 2 ^ n + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hSmall, -, -, -, hNsVac⟩ := h.parts
  by_contra hq1
  by_cases hq : p ∣ 2 ^ n - 1
  · exact hSmall (by simp [GGTableBNbrInnerNineSmallLabel, hq])
  · exact hNsVac (by simp [GGNbrNsVacLabel, GGNbrNsTwF4Label, hq, hq1])

theorem cases {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTableBNbrInnerRound12Label p lab) :
    GGTableBNbrInnerLinearNsLabel p lab ∨ GGTableBNbrInnerUnitaryHypLabel p lab ∨
      GGUnitDvdLabelNo63 p lab ∨ GGTableBNbrInnerRound12ExcRow p lab := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  cases t
  · exact Or.inl (linear hp hn hlab.2.1 h)
  · rcases twA hp hn hlab.2.1 h with h1 | h2 | h3
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h3))))))
  · exact (BC (Or.inl rfl) h).elim
  · exact (BC (Or.inr rfl) h).elim
  · exact (D hlab.2 h).elim
  · exact Or.inr (Or.inl (twD hp hn hlab.2 h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, excE6 h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), excE78 (Or.inl rfl) h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr rfl), excE78 (Or.inr rfl) h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, excF4 h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, excTwE6 h⟩)))))
  · exact (small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h).elim
  · exact (small (Or.inl rfl) h).elim
  · exact (small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, excTwF4 h⟩))))))
  · exact (small (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h).elim
  · exact (small (Or.inr (Or.inl rfl)) h).elim
  · exact (small (Or.inr (Or.inr (Or.inl rfl))) h).elim

end Round12Cl

@[expose] def GGTableBNbrInnerRound12RestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound12Label p lab ∧ ¬ GGTableBNbrInnerLinearNsLabel p lab ∧
    ¬ GGTableBNbrInnerUnitaryHypLabel p lab ∧ ¬ GGUnitDvdLabelNo63 p lab

theorem ggTableBNbrInnerInputOn_round12_of_rest
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound12RestLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound12Label :=
  (ggTableBNbrInnerInputOn_linearNs.or (ggTableBNbrInnerInputOn_unitaryHyp.or
    ((ggTableBNbrInnerInputOn_unitaryDvd LineU.unitaryUniversalCover).or h))).mono
    fun p lab h12 => by
      by_cases hl : GGTableBNbrInnerLinearNsLabel p lab
      · exact Or.inl hl
      · by_cases hh : GGTableBNbrInnerUnitaryHypLabel p lab
        · exact Or.inr (Or.inl hh)
        · by_cases hd : GGUnitDvdLabelNo63 p lab
          · exact Or.inr (Or.inr (Or.inl hd))
          · exact Or.inr (Or.inr (Or.inr ⟨h12, hl, hh, hd⟩))

theorem GGTableBNbrInnerInputOn.mono_guarded {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → S p lab → S' p lab)
    (h : GGTableBNbrInnerInputOn S') : GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hX, lab, hlab, hraw⟩ := h G p B Bs x L D J hcfg y K hnb hN P hP
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hθ.1, fun hS => hθ.2 (hSS' p lab hp hlab hS)⟩

theorem ggTableBNbrInnerInputOn_round12_of_exc
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound12ExcLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound12Label :=
  ggTableBNbrInnerInputOn_round12_of_rest <| h.mono_guarded
    fun _ _ hp hlab ⟨h12, hl, hh, hd⟩ =>
      ⟨h12, (((Round12Cl.cases hp hlab h12).resolve_left hl).resolve_left hh).resolve_left hd⟩

end CFSG.StandardType

end
