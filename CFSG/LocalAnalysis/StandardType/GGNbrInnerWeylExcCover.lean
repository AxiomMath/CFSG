module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem largeEven_prime_not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro hd
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem largeEven_not_dvd_sq_sub_one {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (h1 : ¬ p ∣ q - 1) (h2 : ¬ p ∣ q + 1) : ¬ p ∣ q ^ 2 - 1 := by
  intro h
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [show q ^ 2 - 1 = q ^ 2 - 1 ^ 2 from rfl, sq_tsub_sq]
    ring
  rw [hfac] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsSp {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsSpLabel p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsOrth {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsOrthLabel p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsUnit {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsUnitLabel p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsE7 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsE7Label p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsE6 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsE6Label p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsTwE6 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsTwE6Label p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsF4 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsF4Label p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsE8 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsE8Label p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsTriD4 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsTriD4Label p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_nsVac_of_nsTwF4 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsTwF4Label p lab) : GGNbrNsVacLabel p lab := by
  simp only [GGNbrNsVacLabel]; tauto

theorem ggNbrWeylInnerExcLabel_irred_of_reflSp {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGReflSpLabel p lab) :
    GGNbrWeylInnerIrredLabel p lab := by
  refine ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_irred_of_spNonsplit {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGSpNonsplitLabel p lab) :
    GGNbrWeylInnerIrredLabel p lab := by
  refine ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_irred_of_orthSplit {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGCorFourTwoOrthSplitLabel p lab) :
    GGNbrWeylInnerIrredLabel p lab := by
  refine ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_irred_of_orthNs {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGOrthNsLabel p lab) :
    GGNbrWeylInnerIrredLabel p lab := by
  refine ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_irred_of_excSplit {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGTableBNbrInnerExcSplitLabel p lab) :
    GGNbrWeylInnerIrredLabel p lab := by
  refine ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_irred_of_f4 {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGTableBF4Label p lab) :
    GGNbrWeylInnerIrredLabel p lab := by
  refine ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_irred_of_unitaryCoprime {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGUnitaryCoprimeLabel p lab) :
    GGNbrWeylInnerIrredLabel p lab := by
  refine ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_weylVac_of_nineSmall {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGTableBNbrInnerNineSmallLabel p lab) :
    GGNbrWeylVacLabel p lab := by
  refine Or.inr ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_weylVac_of_nineClassical {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGTableBNbrInnerNineClassicalLabel p lab) :
    GGNbrWeylVacLabel p lab := by
  refine Or.inr ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_weylVac_of_corFourTwo {p : ℕ} {lab : LargeEvenLabel}
    (hpow : GGNbrPowMemLabel p lab) (h : GGCorFourTwoSmallLabel p lab)
    (hs : LargeEvenSplit p lab) :
    GGNbrWeylVacLabel p lab := by
  refine Or.inr ⟨hpow, ?_⟩
  tauto

theorem ggNbrWeylInnerExcLabel_nineSmall_of_G2 {p l n : ℕ} :
    GGTableBNbrInnerNineSmallLabel p (⟨.G2, l, n⟩ : LargeEvenLabel) := by
  simp [GGTableBNbrInnerNineSmallLabel]

theorem ggNbrWeylInnerExcLabel_nineSmall_of_G2der {p l n : ℕ} :
    GGTableBNbrInnerNineSmallLabel p (⟨.G2der, l, n⟩ : LargeEvenLabel) := by
  simp [GGTableBNbrInnerNineSmallLabel]

theorem ggNbrWeylInnerExcLabel_nineSmall_of_twF4der {p l n : ℕ} :
    GGTableBNbrInnerNineSmallLabel p (⟨.twF4der, l, n⟩ : LargeEvenLabel) := by
  simp [GGTableBNbrInnerNineSmallLabel]

theorem ggNbrWeylInnerExcLabel_nineSmall_of_B2der {p l n : ℕ} :
    GGTableBNbrInnerNineSmallLabel p (⟨.B2der, l, n⟩ : LargeEvenLabel) := by
  simp [GGTableBNbrInnerNineSmallLabel]

theorem ggNbrWeylInnerExcLabel_nineSmall_of_A_two {p n : ℕ} :
    GGTableBNbrInnerNineSmallLabel p (⟨.A, 2, n⟩ : LargeEvenLabel) := by
  simp [GGTableBNbrInnerNineSmallLabel]

theorem ggNbrWeylInnerExcLabel_nineSmall_of_twA_two {p n : ℕ} :
    GGTableBNbrInnerNineSmallLabel p (⟨.twA, 2, n⟩ : LargeEvenLabel) := by
  simp [GGTableBNbrInnerNineSmallLabel]

theorem ggNbrWeylInnerExcLabel_nineSmall_of_triD4_three {p l n : ℕ} (h : p = 3) :
    GGTableBNbrInnerNineSmallLabel p (⟨.triD4, l, n⟩ : LargeEvenLabel) := by
  simp [GGTableBNbrInnerNineSmallLabel, h]

theorem ggNbrWeylInnerExcLabel_nineSmall_of_twF4 {p l n : ℕ} (h : p ∣ 2 ^ n - 1) :
    GGTableBNbrInnerNineSmallLabel p (⟨.twF4, l, n⟩ : LargeEvenLabel) := by
  simp [GGTableBNbrInnerNineSmallLabel, h]

theorem ggNbrWeylInnerExcLabel_corFourTwo_of_triD4 {p l n : ℕ} :
    GGCorFourTwoSmallLabel p (⟨.triD4, l, n⟩ : LargeEvenLabel) := by
  simp [GGCorFourTwoSmallLabel, TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel]

theorem ggNbrWeylInnerExcLabel_corFourTwo_of_twF4 {p l n : ℕ} (hp3 : p ≠ 3) :
    GGCorFourTwoSmallLabel p (⟨.twF4, l, n⟩ : LargeEvenLabel) := by
  simp [GGCorFourTwoSmallLabel, TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel, hp3]

theorem ggNbrWeylInnerExcLabel_corFourTwo_of_twD_three {p n : ℕ} (h : p ∣ 2 ^ n - 1) :
    GGCorFourTwoSmallLabel p (⟨.twD, 3, n⟩ : LargeEvenLabel) := by
  simp [GGCorFourTwoSmallLabel, TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel,
    GGStdSubSmallVacLabel, GGTableBTwDThreeLabel, h]

theorem ggNbrWeylInnerExcLabel_split_of_triD4 {p l n : ℕ} (h : p ∣ 2 ^ n - 1) :
    LargeEvenSplit p (⟨.triD4, l, n⟩ : LargeEvenLabel) := by
  simp [LargeEvenSplit, LargeEvenUntwisted, h]

theorem ggNbrWeylInnerExcLabel_split_of_twF4 {p l n : ℕ} (h : p ∣ 2 ^ n + 1) :
    LargeEvenSplit p (⟨.twF4, l, n⟩ : LargeEvenLabel) := by
  simp [LargeEvenSplit, LargeEvenUntwisted, h]

theorem ggNbrWeylInnerExcLabel_split_of_twD {p n : ℕ} (h : p ∣ 2 ^ n - 1) :
    LargeEvenSplit p (⟨.twD, 3, n⟩ : LargeEvenLabel) := by
  simp [LargeEvenSplit, LargeEvenUntwisted, h]

theorem ggNbrWeylInnerExcLabel_unitDvd_of {p l n : ℕ}
    (hpow : GGNbrPowMemLabel p (⟨.twA, l, n⟩ : LargeEvenLabel)) (hl : 3 ≤ l)
    (hq : p ∣ 2 ^ n + 1) (hd : p ∣ l + 1) (hne : ¬ (l = 5 ∧ p = 3)) :
    GGNbrWeylUnitDvdLabel p (⟨.twA, l, n⟩ : LargeEvenLabel) :=
  ⟨hpow, rfl, hl, hq, hd, hne⟩

theorem ggNbrWeylInnerExcLabel_unitThree_of {p n : ℕ}
    (hpow : GGNbrPowMemLabel p (⟨.twA, 3, n⟩ : LargeEvenLabel)) (hq : p ∣ 2 ^ n - 1) :
    GGNbrWeylUnitThreeLabel p (⟨.twA, 3, n⟩ : LargeEvenLabel) := ⟨hpow, rfl, rfl, hq⟩

theorem ggNbrWeylInnerExcLabel_unitFive_of {p n : ℕ}
    (hpow : GGNbrPowMemLabel p (⟨.twA, 5, n⟩ : LargeEvenLabel)) (hq : p ∣ 2 ^ n - 1) :
    GGNbrWeylUnitFiveLabel p (⟨.twA, 5, n⟩ : LargeEvenLabel) := ⟨hpow, rfl, rfl, hq⟩

theorem ggNbrWeylInnerExcLabel_unitSixThree_of {p n : ℕ}
    (hpow : GGNbrPowMemLabel p (⟨.twA, 5, n⟩ : LargeEvenLabel)) (hp3 : p = 3)
    (hq : p ∣ 2 ^ n + 1) :
    GGNbrWeylUnitSixThreeLabel p (⟨.twA, 5, n⟩ : LargeEvenLabel) :=
  ⟨hpow, rfl, rfl, hp3, hq⟩

theorem ggNbrWeylInnerExcLabel_typeA_of {p l n : ℕ}
    (hpow : GGNbrPowMemLabel p (⟨.A, l, n⟩ : LargeEvenLabel)) (hl : 4 ≤ l)
    (hq : p ∣ 2 ^ n - 1) (hd : p ∣ l + 1) :
    GGNbrWeylInnerTypeALabel p (⟨.A, l, n⟩ : LargeEvenLabel) := ⟨hpow, rfl, hl, hq, hd⟩

theorem ggNbrWeylInnerExcLabel_false_A {p l n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.A, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.A, l, n⟩ : LargeEvenLabel)) : False := by
  have hl1 : 1 ≤ l := hlab.2.1
  have hpn : ¬ p ∣ n := by
    have hpw := h.1.2.1
    simp only [GGNbrPowMemLabel, GGNbrLangFieldTwoLabel, GGLinearCoprimeDegLabel,
      GGSpOmegaCoprimeDegLabel, GGExcCoprimeDegLabel, GGCorFourTwoOpenVacLabel,
      GGNbrLangE6CoprimeLabel] at hpw
    simp at hpw
    exact hpw
  rcases lt_or_ge l 2 with hl | hl2
  · have hl1' : l = 1 := by omega
    subst l
    exact h.1.1.1.2 (Or.inl ⟨rfl, rfl⟩)
  · rcases lt_or_ge l 3 with hl | hl3
    · have hl2' : l = 2 := by omega
      subst l
      exact h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineSmall h.1.2.1
        (ggNbrWeylInnerExcLabel_nineSmall_of_A_two))
    · rcases lt_or_ge l 4 with hl | hl4
      · have hl3' : l = 3 := by omega
        subst l
        by_cases hq1 : p ∣ 2 ^ n - 1
        · exact h.1.1.1.1 (Or.inl ⟨rfl, by norm_num, hq1,
            largeEven_prime_not_dvd_four hp hp2⟩)
        · refine h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineClassical h.1.2.1 ?_)
          refine Or.inl ⟨Or.inl ⟨rfl, by norm_num⟩, ?_⟩
          intro j hj hle
          have hle' : 3 * j ≤ 4 := by simpa using hle
          have hj1 : j = 1 := by omega
          subst j
          simpa using hq1
      · by_cases hq1 : p ∣ 2 ^ n - 1
        · by_cases hpl : p ∣ l + 1
          · exact h.1.2.2.2.2 (ggNbrWeylInnerExcLabel_typeA_of h.1.2.1 hl4 hq1 hpl)
          · exact h.1.1.1.1 (Or.inl ⟨rfl, hl2, hq1, hpl⟩)
        · exact h.1.1.2.2 ⟨Or.inl ⟨rfl, hl2⟩, hq1, hpn, Or.inr ⟨rfl, hl4⟩⟩

theorem ggNbrWeylInnerExcLabel_false_twA {p l n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.twA, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.twA, l, n⟩ : LargeEvenLabel)) : False := by
  have hl2 : 2 ≤ l := hlab.2.1
  rcases lt_or_ge l 3 with hl | hl3
  · have hl2' : l = 2 := by omega
    subst l
    exact h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineSmall h.1.2.1
      (ggNbrWeylInnerExcLabel_nineSmall_of_twA_two))
  · rcases lt_or_ge l 4 with hl | hl4
    · have hl3' : l = 3 := by omega
      subst l
      by_cases hq1 : p ∣ 2 ^ n - 1
      · exact h.2.2.1 (ggNbrWeylInnerExcLabel_unitThree_of h.1.2.1 hq1)
      · by_cases hq2 : p ∣ 2 ^ n + 1
        · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_unitaryCoprime h.1.2.1
            (Or.inl ⟨rfl, hq2, largeEven_prime_not_dvd_four hp hp2⟩))
        · refine h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineClassical h.1.2.1 ?_)
          refine Or.inr (Or.inl ⟨Or.inl ⟨rfl, by norm_num⟩, ?_⟩)
          intro j hj hle
          have hle' : 3 * j ≤ 4 := by simpa using hle
          have hj1 : j = 1 := by omega
          subst j
          simp only [pow_one]
          exact largeEven_not_dvd_sq_sub_one (q := 2 ^ n) hp Nat.one_le_two_pow hq1 hq2
    · have hns : ¬ GGNbrNsUnitLabel p (⟨.twA, l, n⟩ : LargeEvenLabel) :=
        fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsUnit hx)
      have hsplit : p ∣ 2 ^ n + 1 ∨ (l = 5 ∧ p ∣ 2 ^ n - 1) := by
        by_cases hq2 : p ∣ 2 ^ n + 1
        · exact Or.inl hq2
        · refine Or.inr ?_
          by_contra hcon
          exact hns ⟨rfl, hl4, hq2, fun hl5 hq1 => hcon ⟨hl5, hq1⟩⟩
      rcases hsplit with hq2 | ⟨hl5, hq1⟩
      · by_cases hpl : p ∣ l + 1
        · by_cases h53 : l = 5 ∧ p = 3
          · obtain ⟨rfl, rfl⟩ := h53
            exact h.2.2.2.2 (ggNbrWeylInnerExcLabel_unitSixThree_of h.1.2.1 rfl hq2)
          · exact h.2.1 (ggNbrWeylInnerExcLabel_unitDvd_of h.1.2.1 (by omega) hq2 hpl h53)
        · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_unitaryCoprime h.1.2.1
            (Or.inl ⟨rfl, hq2, hpl⟩))
      · subst l
        exact h.2.2.2.1 (ggNbrWeylInnerExcLabel_unitFive_of h.1.2.1 hq1)

theorem ggNbrWeylInnerExcLabel_false_B {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.B, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.B, l, n⟩ : LargeEvenLabel)) : False := by
  have hns : ¬ GGNbrNsSpLabel p (⟨.B, l, n⟩ : LargeEvenLabel) :=
    fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsSp hx)
  have hsplit : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    by_contra hcon
    push Not at hcon
    exact hns ⟨Or.inl rfl, hcon.1, hcon.2⟩
  rcases hsplit with hq1 | hq2
  · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_reflSp h.1.2.1 ⟨Or.inl rfl, hq1⟩)
  · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_spNonsplit h.1.2.1 ⟨Or.inl rfl, hq2⟩)

theorem ggNbrWeylInnerExcLabel_false_C {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.C, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.C, l, n⟩ : LargeEvenLabel)) : False := by
  have hns : ¬ GGNbrNsSpLabel p (⟨.C, l, n⟩ : LargeEvenLabel) :=
    fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsSp hx)
  have hsplit : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    by_contra hcon
    push Not at hcon
    exact hns ⟨Or.inr rfl, hcon.1, hcon.2⟩
  rcases hsplit with hq1 | hq2
  · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_reflSp h.1.2.1 ⟨Or.inr rfl, hq1⟩)
  · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_spNonsplit h.1.2.1 ⟨Or.inr rfl, hq2⟩)

theorem ggNbrWeylInnerExcLabel_false_D {p l n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.D, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.D, l, n⟩ : LargeEvenLabel)) : False := by
  have hl3 : 3 ≤ l := hlab.2
  rcases lt_or_ge l 4 with hl | hl4
  · have hl3' : l = 3 := by omega
    subst l
    have hn0 : 1 ≤ n := hlab.1
    have hq1 : ¬ p ∣ 2 ^ n - 1 := fun hq =>
      h.1.1.1.1 (Or.inr ⟨rfl, rfl, hq, largeEven_prime_not_dvd_four hp hp2⟩)
    have hpn : ¬ p ∣ n := by
      have hpw := h.1.2.1
      simp only [GGNbrPowMemLabel, GGNbrLangFieldTwoLabel, GGLinearCoprimeDegLabel,
        GGSpOmegaCoprimeDegLabel, GGExcCoprimeDegLabel, GGCorFourTwoOpenVacLabel,
        GGNbrLangE6CoprimeLabel] at hpw
      simp at hpw
      exact hpw
    rcases lt_or_ge n 2 with hn | hn2
    · have hn1 : n = 1 := by omega
      subst n
      refine h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineClassical h.1.2.1 ?_)
      refine Or.inl ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      intro j hj hle
      have hle' : 3 * j ≤ 4 := by simpa using hle
      have hj1 : j = 1 := by omega
      subst j
      simpa using hq1
    · exact h.1.1.2.2 ⟨Or.inr ⟨rfl, rfl⟩, hq1, hpn, Or.inl ⟨hn2, by simp⟩⟩
  · have hns : ¬ GGNbrNsOrthLabel p (⟨.D, l, n⟩ : LargeEvenLabel) :=
      fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsOrth hx)
    have hsplit : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
      by_contra hcon
      push Not at hcon
      exact hns ⟨Or.inl rfl, hl4, hcon.1, hcon.2⟩
    rcases hsplit with hq1 | hq2
    · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_orthSplit h.1.2.1
        ⟨Or.inl rfl, hl4, hq1⟩)
    · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_orthNs h.1.2.1
        ⟨Or.inl rfl, hl4, hq2⟩)

theorem ggNbrWeylInnerExcLabel_false_twD {p l n : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.twD, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.twD, l, n⟩ : LargeEvenLabel)) : False := by
  have hl2 : 2 ≤ l := hlab.2
  rcases lt_or_ge l 3 with hl | hl3
  · have hl2' : l = 2 := by omega
    subst l
    exact h.1.1.1.2 (Or.inr ⟨rfl, rfl⟩)
  · rcases lt_or_ge l 4 with hl | hl4
    · have hl3' : l = 3 := by omega
      subst l
      by_cases hq2 : p ∣ 2 ^ n + 1
      · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_unitaryCoprime h.1.2.1
          (Or.inr ⟨rfl, rfl, hq2⟩))
      · by_cases hq1 : p ∣ 2 ^ n - 1
        · refine h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_corFourTwo h.1.2.1
            (ggNbrWeylInnerExcLabel_corFourTwo_of_twD_three hq1)
            (ggNbrWeylInnerExcLabel_split_of_twD hq1))
        · refine h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineClassical h.1.2.1 ?_)
          refine Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩)
          intro j hj hle
          have hle' : 3 * j ≤ 4 := by simpa using hle
          have hj1 : j = 1 := by omega
          subst j
          simp only [pow_one]
          exact largeEven_not_dvd_sq_sub_one (q := 2 ^ n) hp Nat.one_le_two_pow hq1 hq2
    · have hns : ¬ GGNbrNsOrthLabel p (⟨.twD, l, n⟩ : LargeEvenLabel) :=
        fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsOrth hx)
      have hsplit : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
        by_contra hcon
        push Not at hcon
        exact hns ⟨Or.inr rfl, hl4, hcon.1, hcon.2⟩
      rcases hsplit with hq1 | hq2
      · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_orthSplit h.1.2.1
          ⟨Or.inr rfl, hl4, hq1⟩)
      · exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_orthNs h.1.2.1
          ⟨Or.inr rfl, hl4, hq2⟩)

theorem ggNbrWeylInnerExcLabel_false_triD4 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.triD4, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.triD4, l, n⟩ : LargeEvenLabel)) : False := by
  by_cases hp3 : p = 3
  · exact h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineSmall h.1.2.1
      (ggNbrWeylInnerExcLabel_nineSmall_of_triD4_three hp3))
  · have hns : ¬ GGNbrNsTriD4Label p (⟨.triD4, l, n⟩ : LargeEvenLabel) :=
      fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsTriD4 hx)
    have hq1 : p ∣ 2 ^ n - 1 := by
      by_contra hq
      exact hns ⟨rfl, hq, hp3⟩
    exact h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_corFourTwo h.1.2.1
      (ggNbrWeylInnerExcLabel_corFourTwo_of_triD4)
      (ggNbrWeylInnerExcLabel_split_of_triD4 hq1))

theorem ggNbrWeylInnerExcLabel_false_G2 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.G2, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.G2, l, n⟩ : LargeEvenLabel)) : False :=
  h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineSmall h.1.2.1
    (ggNbrWeylInnerExcLabel_nineSmall_of_G2))

theorem ggNbrWeylInnerExcLabel_false_twB2 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.twB2, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.twB2, l, n⟩ : LargeEvenLabel)) : False :=
  h.1.1.2.1 (Or.inl rfl)

theorem ggNbrWeylInnerExcLabel_false_B2der {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.B2der, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.B2der, l, n⟩ : LargeEvenLabel)) : False :=
  h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineSmall h.1.2.1
    (ggNbrWeylInnerExcLabel_nineSmall_of_B2der))

theorem ggNbrWeylInnerExcLabel_false_G2der {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.G2der, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.G2der, l, n⟩ : LargeEvenLabel)) : False :=
  h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineSmall h.1.2.1
    (ggNbrWeylInnerExcLabel_nineSmall_of_G2der))

theorem ggNbrWeylInnerExcLabel_false_twF4der {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.twF4der, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.twF4der, l, n⟩ : LargeEvenLabel)) : False :=
  h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineSmall h.1.2.1
    (ggNbrWeylInnerExcLabel_nineSmall_of_twF4der))

theorem ggNbrWeylInnerExcLabel_E6 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.E6, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.E6, l, n⟩ : LargeEvenLabel)) :
    GGNbrWeylE6Label p (⟨.E6, l, n⟩ : LargeEvenLabel) := by
  have hns : ¬ GGNbrNsE6Label p (⟨.E6, l, n⟩ : LargeEvenLabel) :=
    fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsE6 hx)
  have hcases : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) ∨ (n = 1 ∧ p = 7) := by
    by_contra hcon
    push Not at hcon
    exact hns ⟨rfl, hcon.1, (fun h => hcon.2.1 h.1 h.2), (fun h => hcon.2.2 h.1 h.2)⟩
  refine ⟨h.1.2.1, rfl, ?_⟩
  rcases hcases with hq1 | ⟨hn1, hp3⟩ | ⟨hn1, hp7⟩
  · left
    refine ⟨?_, hq1⟩
    by_contra hp3
    exact h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_excSplit h.1.2.1
      ⟨Or.inl ⟨rfl, hp3⟩, hq1⟩)
  · exact Or.inr ⟨hn1, Or.inl hp3⟩
  · exact Or.inr ⟨hn1, Or.inr hp7⟩

theorem ggNbrWeylInnerExcLabel_twE6 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.twE6, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.twE6, l, n⟩ : LargeEvenLabel)) :
    GGNbrWeylTwE6Label p (⟨.twE6, l, n⟩ : LargeEvenLabel) := by
  have hns : ¬ GGNbrNsTwE6Label p (⟨.twE6, l, n⟩ : LargeEvenLabel) :=
    fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsTwE6 hx)
  have hcases : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    by_contra hcon
    push Not at hcon
    exact hns ⟨rfl, hcon.1, hcon.2⟩
  exact ⟨h.1.2.1, rfl, hcases⟩

theorem ggNbrWeylInnerExcLabel_E7 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.E7, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.E7, l, n⟩ : LargeEvenLabel)) :
    GGNbrWeylExcPlusLabel p (⟨.E7, l, n⟩ : LargeEvenLabel) := by
  have hns : ¬ GGNbrNsE7Label p (⟨.E7, l, n⟩ : LargeEvenLabel) :=
    fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsE7 hx)
  have hcases : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    by_contra hcon
    push Not at hcon
    exact hns ⟨rfl, hcon.1, hcon.2⟩
  have hq2 : p ∣ 2 ^ n + 1 := by
    rcases hcases with hq1 | hq2
    · exact (h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_excSplit h.1.2.1
        ⟨Or.inr (Or.inl rfl), hq1⟩)).elim
    · exact hq2
  exact ⟨h.1.2.1, Or.inl rfl, hq2⟩

theorem ggNbrWeylInnerExcLabel_E8 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.E8, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.E8, l, n⟩ : LargeEvenLabel)) :
    GGNbrWeylExcPlusLabel p (⟨.E8, l, n⟩ : LargeEvenLabel) := by
  have hns : ¬ GGNbrNsE8Label p (⟨.E8, l, n⟩ : LargeEvenLabel) :=
    fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsE8 hx)
  have hcases : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    by_contra hcon
    push Not at hcon
    exact hns ⟨rfl, hcon.1, hcon.2⟩
  have hq2 : p ∣ 2 ^ n + 1 := by
    rcases hcases with hq1 | hq2
    · exact (h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_excSplit h.1.2.1
        ⟨Or.inr (Or.inr rfl), hq1⟩)).elim
    · exact hq2
  exact ⟨h.1.2.1, Or.inr (Or.inl rfl), hq2⟩

theorem ggNbrWeylInnerExcLabel_F4 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.F4, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.F4, l, n⟩ : LargeEvenLabel)) :
    GGNbrWeylExcPlusLabel p (⟨.F4, l, n⟩ : LargeEvenLabel) := by
  have hns : ¬ GGNbrNsF4Label p (⟨.F4, l, n⟩ : LargeEvenLabel) :=
    fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsF4 hx)
  have hcases : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    by_contra hcon
    push Not at hcon
    exact hns ⟨rfl, hcon.1, hcon.2⟩
  have hq2 : p ∣ 2 ^ n + 1 := by
    rcases hcases with hq1 | hq2
    · exact (h.1.2.2.2.1 (ggNbrWeylInnerExcLabel_irred_of_f4 h.1.2.1 ⟨rfl, hq1⟩)).elim
    · exact hq2
  exact ⟨h.1.2.1, Or.inr (Or.inr rfl), hq2⟩

theorem ggNbrWeylInnerExcLabel_twF4 {p l n : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 (⟨.twF4, l, n⟩ : LargeEvenLabel))
    (h : GGNbrWeylInnerExcLabel p (⟨.twF4, l, n⟩ : LargeEvenLabel)) :
    GGNbrWeylTwF4Label p (⟨.twF4, l, n⟩ : LargeEvenLabel) := by
  have hns : ¬ GGNbrNsTwF4Label p (⟨.twF4, l, n⟩ : LargeEvenLabel) :=
    fun hx => h.1.2.2.1 (ggNbrWeylInnerExcLabel_nsVac_of_nsTwF4 hx)
  have hcases : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    by_contra hcon
    push Not at hcon
    exact hns ⟨rfl, hcon.1, hcon.2⟩
  have hq2 : p ∣ 2 ^ n + 1 := by
    rcases hcases with hq1 | hq2
    · exact (h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_nineSmall h.1.2.1
        (ggNbrWeylInnerExcLabel_nineSmall_of_twF4 hq1))).elim
    · exact hq2
  have hp3 : p = 3 := by
    by_contra hp3
    exact (h.1.1.2.1 (ggNbrWeylInnerExcLabel_weylVac_of_corFourTwo h.1.2.1
      (ggNbrWeylInnerExcLabel_corFourTwo_of_twF4 hp3)
      (ggNbrWeylInnerExcLabel_split_of_twF4 hq2))).elim
  exact ⟨h.1.2.1, rfl, hp3, hq2⟩

theorem ggNbrWeylInnerExcLabel_cases {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrWeylInnerExcLabel p lab) :
    GGNbrWeylE6Label p lab ∨ GGNbrWeylTwE6Label p lab ∨ GGNbrWeylExcPlusLabel p lab ∨
      GGNbrWeylTwF4Label p lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  · exact (ggNbrWeylInnerExcLabel_false_A hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_twA hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_B hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_C hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_D hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_twD hp hp2 hlab h).elim
  · exact Or.inl (ggNbrWeylInnerExcLabel_E6 hp hp2 hlab h)
  · exact Or.inr (Or.inr (Or.inl (ggNbrWeylInnerExcLabel_E7 hp hp2 hlab h)))
  · exact Or.inr (Or.inr (Or.inl (ggNbrWeylInnerExcLabel_E8 hp hp2 hlab h)))
  · exact Or.inr (Or.inr (Or.inl (ggNbrWeylInnerExcLabel_F4 hp hp2 hlab h)))
  · exact Or.inr (Or.inl (ggNbrWeylInnerExcLabel_twE6 hp hp2 hlab h))
  · exact (ggNbrWeylInnerExcLabel_false_triD4 hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_G2 hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_twB2 hp hp2 hlab h).elim
  · exact Or.inr (Or.inr (Or.inr (ggNbrWeylInnerExcLabel_twF4 hp hp2 hlab h)))
  · exact (ggNbrWeylInnerExcLabel_false_B2der hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_G2der hp hp2 hlab h).elim
  · exact (ggNbrWeylInnerExcLabel_false_twF4der hp hp2 hlab h).elim

end CFSG.StandardType

end
