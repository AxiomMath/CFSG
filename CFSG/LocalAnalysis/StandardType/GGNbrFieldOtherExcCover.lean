module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCover
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggFieldOtherC9Label_exc_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hc : GGFieldOtherC9Label p lab)
    (hnc : ¬ GGFieldClassicalTag lab) :
    p ∣ lab.n ∧ ((lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1) ∨
      ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ 7 ≤ p ∧ p ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .F4 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .G2 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .triD4 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n + 1)) := by
  have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
  have hp6 : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
  have hp1 : 2 ≤ p := hp.two_le
  obtain ⟨t, r, n⟩ := lab
  simp only [GGFieldOtherC9Label, GGNbrWeylFieldOtherOpenLabel, GGNbrWeylFieldOtherLabel,
    GGNbrWeylFieldVacOtherLabel, GGNbrVacU3Label, GGNbrVacL4Label, GGNbrVacU4Label,
    GGNbrVacG2Label, GGNbrVacTwF4Label, GGNbrWeylFieldRestLabel, GGNbrWeylFieldLabel,
    GGNbrWeylFieldVacA2Label, GGNbrWeylRest12Label, GGNbrPowMemLabel, GGNbrLangFieldTwoLabel,
    GGExcCoprimeDegLabel, GGCorFourTwoOpenVacLabel, GGNbrLangE6CoprimeLabel, GGNbrNsVacLabel,
    GGNbrWeylFieldRowLabel, GGNbrWeylTriD4TwoLabel, GGNbrWeylOpenFamily, GGFieldFixLabel,
    GGFieldFixRowLabel, GGFieldFixNsLabel, GGFieldFixNsRowLabel, GGFieldFixD4Label,
    GGNbrWeylRestLabel, GGNbrWeylVacLabel, GGNbrLinearNsLabel,
    GGLinearCoprimeDegLabel, GGSpOmegaCoprimeDegLabel, GGNbrNsSpLabel, GGNbrNsOrthLabel,
    GGNbrNsLinLabel, GGNbrNsUnitLabel, GGNbrNsE7Label, GGNbrNsE6Label, GGNbrNsTwE6Label,
    GGNbrNsF4Label, GGNbrNsE8Label, GGNbrNsTriD4Label, GGNbrNsTwF4Label] at hc
  simp only [GGFieldClassicalTag] at hnc
  simp only [LargeEvenInLambda2] at hlab
  cases t <;> simp at hnc hc hlab ⊢
  case E6 =>
    obtain ⟨⟨⟨-, ⟨hn1, hpn⟩, hD⟩, hE⟩, hF⟩ := hc
    by_cases h : p ∣ 2 ^ n - 1
    · obtain rfl := hF hpn h
      exact hE rfl h
    · exact hn1 (hD h fun h1 => absurd h1 hn1).1
  case E7 =>
    obtain ⟨⟨⟨-, ⟨-, hpn⟩, hD⟩, hE⟩, hF⟩ := hc
    have hplus := hD (hF hpn)
    refine ⟨hpn, ?_, hplus⟩
    by_contra hlt
    exact hE (by omega) hplus
  case E8 =>
    obtain ⟨⟨⟨-, ⟨-, hpn⟩, hD⟩, hE⟩, hF⟩ := hc
    have hplus := hD (hF hpn)
    refine ⟨hpn, ?_, hplus⟩
    by_contra hlt
    exact hE (by omega) hplus
  case F4 =>
    obtain ⟨⟨⟨-, ⟨-, hpn⟩, hD⟩, hE⟩, hF⟩ := hc
    have hplus := hD (hF hpn)
    refine ⟨hpn, ?_, hplus⟩
    have h3 : p ≠ 3 := fun h3 => hE h3 hplus
    omega
  case twE6 =>
    obtain ⟨⟨-, hpn, hD⟩, ⟨hE1, hE2⟩, hE3⟩ := hc
    have h3 : p ≠ 3 := by
      rintro rfl
      rcases ggThree_dvd_two_pow_sub_or_add n with h | h
      · exact hE1 rfl h
      · exact hE3 rfl h
    have h5 : 5 ≤ p := by omega
    refine ⟨hpn, h5, ?_⟩
    by_contra h
    exact hE2 h5 (hD h)
  case triD4 =>
    obtain ⟨hn1, -⟩ := hlab
    obtain ⟨⟨⟨hA, hC⟩, hpn, hD⟩, hG, hle⟩ := hc
    have h3 : p ≠ 3 := by
      rintro rfl
      have := hle rfl
      exact hG hA.1 hA.2 hC hpn hD rfl (by omega)
    refine ⟨hpn h3, h3, ?_⟩
    by_contra h
    exact h3 (hD h)
  case G2 =>
    obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hpn⟩, hG⟩, h6⟩ := hc
    have hm := hG hA hB hC hpn
    refine ⟨hpn, ?_, hm⟩
    have h3 : p ≠ 3 := by
      rintro rfl
      have h2 := even_iff_two_dvd.mp ((gffa2_three_dvd_pow_sub_one_iff n).mp hm)
      exact h6 rfl (by omega)
    omega
  case twF4 =>
    obtain ⟨⟨⟨hA, hC⟩, hpn, hD⟩, hG⟩ := hc
    exact ⟨hpn, hG hA.1 hA.2 hC hpn hD⟩
  case B2der => exact hc.2 hlab.2.2
  case G2der => exact hc.2 hlab.2.2
  case twF4der => exact hc.2 hlab.2.2

end CFSG.StandardType

end
