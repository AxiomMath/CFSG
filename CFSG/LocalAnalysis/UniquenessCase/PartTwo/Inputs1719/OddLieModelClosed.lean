module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.Q3.Q3OFCovEven
public import CFSG.ClassicalInvolution.Q3.Q3OFCovK
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinOddCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift
public import CFSG.LieType.Steinberg.CentralExt.TrialityClosed
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SpinSevenThree
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

abbrev IsSmallThreeTag (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSp ∧ n = 2) ∨ (t = .POmegaOdd ∧ n = 3) ∨ t = .G2 ∨ (t = .PSU ∧ n = 4)


theorem modelUniv_closed {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hq : 5 ≤ p ^ e) (hA1 : ¬ (t = .PSL ∧ n = 2)) (E : Type) [Group E] [Finite E]
    (π : E →* (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).K →* E, ∀ g, π (σ g) = g := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, he, hrest⟩ := hadm
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hF5 : 5 ≤ Nat.card (GaloisField p e) := hcard ▸ hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  cases t
  case PSL =>
    obtain ⟨hn2, -, -⟩ := hrest
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 2 ≤ m := by
      by_contra h
      exact hA1 ⟨rfl, by omega⟩
    exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
      (F := GaloisField p e) hm hF5 hπ hcen
  case PSU =>
    obtain ⟨hn3, hn32⟩ := hrest
    have hF := CFSG.LieType.Universal.card_galoisField_two_mul p e he
    have hM := (rfl : CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p e hp =
      CFSG.ClassicalInvolution.ModelFacts.modelUniv .PSU n p e hp).trans
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv_PSU (hp := ⟨hp⟩) he)
    refine CFSG.ClassicalInvolution.Q3.Q3OF.closed_of_univ_eq hM ?_ E π hπ hcen
    intro E _ _ π hπ hcen
    by_cases hev : Even n
    · have hn4 : 4 ≤ n := by
        obtain ⟨k, rfl⟩ := hev
        omega
      exact CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_central hF hev hn4
        (by omega) hπ hcen
    · refine CFSG.SeitzReduction.F4Pilot.forall_exists_section_of_mulEquiv
        (CFSG.LieType.Universal.Unitary.equivStatedSU hF n) ?_ E π hπ hcen
      intro E _ _ π hπ hcen
      exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hF he
        hn3 hev hn32 hπ hcen
  case PSp =>
    obtain ⟨hn2, -⟩ := hrest
    exact CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_central
      (F := GaloisField p e) hn2 hF5 hπ hcen
  case POmegaOdd =>
    obtain ⟨hn3, -⟩ := hrest
    exact CFSG.LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_exists_section_of_central
      (K := GaloisField p e) h2 hn3 hF5 hπ hcen
  case POmegaPlus =>
    have hn3 : 3 ≤ n := by omega
    have hM := (rfl : CFSG.ClassicalInvolution.Generic.modelUniv .POmegaPlus n p e hp =
      CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e hp).trans
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (hp := ⟨hp⟩) (f := e) hn3)
    refine CFSG.ClassicalInvolution.Q3.Q3OF.closed_of_univ_eq hM ?_ E π hπ hcen
    intro E _ _ π hπ hcen
    exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_exists_section_of_central
      (K := GaloisField p e) hn3 (by omega) hπ hcen
  case POmegaMinus =>
    exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_central
      (CFSG.LieType.Universal.minusCoeffs_irr p e) hrest (by omega) hπ hcen
  case G2 =>
    exact CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_exists_section_of_central
      (K := GaloisField p e) hF5 hπ hcen
  case F4 =>
    exact CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_exists_section_of_central
      (K := GaloisField p e) hF5 hπ hcen
  case E6 =>
    exact CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_exists_section_of_central
      (k := GaloisField p e) hF5 hπ hcen
  case E7 =>
    exact CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e7_exists_section_of_central
      (k := GaloisField p e) hF5 hπ hcen
  case E8 =>
    exact CFSG.LieType.Steinberg.CentralExt.AdjointClosed.e8_exists_section_of_central
      (K := GaloisField p e) hF5 hπ hcen
  case twistedE6 =>
    exact CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_exists_section_of_central
      (CFSG.LieType.Steinberg.Exceptional.frobQ p e) hq
      (CFSG.LieType.Universal.card_galoisField_two_mul p e he)
      (fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply p e c) hπ hcen
  case trialityD4 =>
    have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
      rw [GaloisField.card p (3 * e) (by omega), ← pow_mul, mul_comm]
    exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.triality_exists_section_of_central
      (K := GaloisField p (3 * e)) (q := p ^ e) (by omega) hK
      (fun c => iterateFrobenius_def p e c) hπ hcen
  all_goals exact absurd hfund (by simp [CFSG.ClassicalInvolution.Generic.IsFundTag])


theorem modelUniv_closed_three {t : StatedLieTag} {n : ℕ}
    (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (E : Type) [Group E] [Finite E]
    (π : E →* (CFSG.ClassicalInvolution.Generic.modelUniv t n 3 1 Nat.prime_three).K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h3 : ¬ 3 ∣ Nat.card π.ker) :
    ∃ σ : (CFSG.ClassicalInvolution.Generic.modelUniv t n 3 1 Nat.prime_three).K →* E,
      ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC : (3 : ℕ).Coprime (Nat.card π.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hadm' := hadm
  obtain ⟨-, -, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn2, -, hn23⟩ := hrest
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 2 ≤ m := by
      by_contra h
      exact hn23 (by rw [show m = 1 by omega]; rfl)
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_psl hm E π hπ hcen
  case PSU =>
    obtain ⟨hn3, -⟩ := hrest
    by_cases hev : Even n
    · by_cases hn4 : n = 4
      · subst hn4
        exact CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_coprime
          (F := GaloisField 3 2) (p := 3) (f := 1) CFSG.ClassicalInvolution.Q3.Q3W.card_gf9
          ⟨2, rfl⟩ (by norm_num) hπ hcen hC
      · exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_psu_even hev
          (by obtain ⟨k, rfl⟩ := hev; omega) E π hπ hcen
    · exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_psu_odd hadm' hev E π hπ hcen
  case PSp =>
    obtain ⟨hn2, -⟩ := hrest
    by_cases hn : n = 2
    · subst hn
      exact CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_coprime
        (K := GaloisField 3 1) (p := 3) E π hπ hcen hC
    · exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_psp (by omega) E π hπ hcen
  case POmegaOdd =>
    obtain ⟨hn3, -⟩ := hrest
    by_cases hn : n = 3
    · subst hn
      exact CFSG.LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_exists_section_of_coprime
        (K := GaloisField 3 1) (p := 3) (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField
          1 (by norm_num)) le_rfl hπ hcen hC
    · exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_pomegaOdd (by omega) E π hπ hcen
  case POmegaPlus =>
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_pomegaPlus hrest E π hπ hcen
  case POmegaMinus =>
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_pomegaMinus hrest E π hπ hcen
  case G2 =>
    exact CFSG.LieType.Steinberg.CentralExt.G2Four.g2_exists_section_of_coprime
      (K := GaloisField 3 1) (p := 3) E π hπ hcen hC
  case F4 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_f4 n E π hπ hcen
  case E6 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_e6 n E π hπ hcen
  case E7 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_e7 n E π hπ hcen
  case E8 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_e8 n E π hπ hcen
  case twistedE6 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_twistedE6 n E π hπ hcen
  case trialityD4 =>
    subst hrest
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_trialityD4 E π hπ hcen
  all_goals exact absurd hfund (by simp [CFSG.ClassicalInvolution.Generic.IsFundTag])

theorem modelUniv_closed_three_full {t : StatedLieTag} {n : ℕ}
    (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hex : ¬ IsSmallThreeTag t n) (E : Type) [Group E] [Finite E]
    (π : E →* (CFSG.ClassicalInvolution.Generic.modelUniv t n 3 1 Nat.prime_three).K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : (CFSG.ClassicalInvolution.Generic.modelUniv t n 3 1 Nat.prime_three).K →* E,
      ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm' := hadm
  obtain ⟨-, -, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn2, -, hn23⟩ := hrest
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 2 ≤ m := by
      by_contra h
      exact hn23 (by rw [show m = 1 by omega]; rfl)
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_psl hm E π hπ hcen
  case PSU =>
    obtain ⟨hn3, -⟩ := hrest
    by_cases hev : Even n
    · have hn4 : n ≠ 4 := fun h => hex (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
      exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_psu_even hev
        (by obtain ⟨k, rfl⟩ := hev; omega) E π hπ hcen
    · exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_psu_odd hadm' hev E π hπ hcen
  case PSp =>
    obtain ⟨hn2, -⟩ := hrest
    have hn : n ≠ 2 := fun h => hex (Or.inl ⟨rfl, h⟩)
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_psp (by omega) E π hπ hcen
  case POmegaOdd =>
    obtain ⟨hn3, -⟩ := hrest
    have hn : n ≠ 3 := fun h => hex (Or.inr (Or.inl ⟨rfl, h⟩))
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_pomegaOdd (by omega) E π hπ hcen
  case POmegaPlus =>
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_pomegaPlus hrest E π hπ hcen
  case POmegaMinus =>
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_pomegaMinus hrest E π hπ hcen
  case G2 => exact absurd (Or.inr (Or.inr (Or.inl rfl))) hex
  case F4 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_f4 n E π hπ hcen
  case E6 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_e6 n E π hπ hcen
  case E7 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_e7 n E π hπ hcen
  case E8 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_e8 n E π hπ hcen
  case twistedE6 => exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_twistedE6 n E π hπ hcen
  case trialityD4 =>
    subst hrest
    exact CFSG.ClassicalInvolution.Q3.Q3OF.kindClosed3_trialityD4 E π hπ hcen
  all_goals exact absurd hfund (by simp [CFSG.ClassicalInvolution.Generic.IsFundTag])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie
