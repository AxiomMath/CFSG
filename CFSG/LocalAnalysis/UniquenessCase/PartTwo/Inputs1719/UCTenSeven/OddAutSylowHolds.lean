module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylowLow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixClassical
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixExceptional
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixTwisted
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowG2D4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowPSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowPOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowExceptional
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixLinear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowPSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixUnitary
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowPSU
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeMinus
public import CFSG.LieType.Universal.Catalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram isPrimeFormGram_idGram)

theorem autSylowAt_projectiveSL_of_four_le
    {K : Type} [Field K] [Finite K] {n r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) (hn : 4 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    AutSylowAt (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) p := by
  have : Fact r.Prime := ⟨hr⟩
  have : CharP K r := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let : Algebra (ZMod r) K := ZMod.algebra K r
  let ρ : K ≃+* GaloisField r f := (GaloisField.algEquivGaloisField r f hK).toRingEquiv
  refine autSylowAt_of_mulEquiv (CFSG.SeitzReduction.OmegaPilot.pslRingCongr ρ n) ?_
  exact autSylowAt_of_normSylowIn
    (CFSG.RankThree.PartTwo.KFacts.innAut_le_linearAutGroup n (GaloisField r f))
    (normSylowIn_projectiveSL_galois hr2 hf hn hp hp5)
    (fixesSylowOutside_projectiveSL hr hr2 hf (GaloisField.card r f (by omega)) (by omega) hp
      hp5)

theorem autSylowAt_projectiveSL_of_three_le
    {K : Type} [Field K] [Finite K] {n r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    AutSylowAt (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) p := by
  obtain rfl | hn4 : n = 3 ∨ 4 ≤ n := by omega
  · exact autSylowAt_projectiveSL_three hr hr2 hf hK (hp.odd_of_ne_two (by omega))
  · exact autSylowAt_projectiveSL_of_four_le hr hr2 hf hK hn4 hp hp5

theorem autSylowAt_of_statedPSU_of_four_le
    {X : Type} [Group X] [Finite X] {n r f : ℕ}
    (hr2 : r ≠ 2) (h : CFSG.Open.StatedClassicalModel X .PSU n r f) (hn : 4 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    AutSylowAt X p := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact r.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hF : Nat.card (GaloisField r (2 * f)) = (r ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul r f hf
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField r (2 * f)) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField r (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF]
  let φ : K ≃+* GaloisField r (2 * f) := FiniteField.ringEquivOfCardEq hc
  let E : CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) K) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) (GaloisField r (2 * f))) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin n) φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ n (r ^ f))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  let hU : UnitaryFieldData r f (GaloisField r (2 * f)) :=
    ⟨hadm.1, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  let eP : primeFormP hU (idGram (GaloisField r (2 * f)) n) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) (GaloisField r (2 * f))) :=
    (Classical.choice (nonempty_primeFormP_mulEquiv hU isPrimeFormGram_idGram)).trans
      (unitaryPSUEquiv hU (by omega))
  refine autSylowAt_of_mulEquiv ((e.trans E).trans eP.symm) ?_
  refine autSylowAt_of_normSylowIn ?_ (normSylowIn_primeFormP_galois hr2 hf hU hn hp hp5)
    (fixesSylowOutside_primeFormP hU hr2 (by omega) hp hp5)
  intro α hα
  obtain ⟨s, rfl⟩ := (mem_inner_primeFormP hU _ α).mp hα
  exact ⟨_, rfl⟩

theorem autSylowAt_of_statedPSU
    {X : Type} [Group X] [Finite X] {n r f : ℕ} (hr2 : r ≠ 2)
    (h : CFSG.Open.StatedClassicalModel X .PSU n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    AutSylowAt X p := by
  have hn : 3 ≤ n := h.1.2.2.1
  obtain rfl | hn4 : n = 3 ∨ 4 ≤ n := by omega
  · exact autSylowAt_of_statedPSU_three hr2 h (hp.odd_of_ne_two (by omega))
  · exact autSylowAt_of_statedPSU_of_four_le hr2 h hn4 hp hp5

theorem normSylowAt_pomega_of_lieModel
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {t : CFSG.Open.StatedLieTag} {n r f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hr2 : r ≠ 2) (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hX : CFSG.Blueprint.LieModel X t n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormSylowAt X p :=
  normSylowAt_pomega hXs ht hr2 hadm hX hp hp5

theorem normSylowAt_exceptional_of_lieModel
    {X : Type} [Group X] [Finite X]
    (hXs : IsSimpleGroup X) {t : CFSG.Open.StatedLieTag} {n r f : ℕ}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hr2 : r ≠ 2) (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hX : CFSG.Blueprint.LieModel X t n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormSylowAt X p :=
  normSylowAt_exceptional hXs ht hr2 hadm hX hp hp5

theorem normSylowAt_of_lieModel
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {t : CFSG.Open.StatedLieTag} {n r f : ℕ} (ht : t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .twistedG2)
    (hr2 : r ≠ 2) (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hX : CFSG.Blueprint.LieModel X t n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormSylowAt X p := by
  cases t with
  | PSL => exact absurd rfl ht.1
  | PSU => exact absurd rfl ht.2.1
  | twistedG2 => exact absurd rfl ht.2.2
  | G2 => exact normSylowAt_G2 hr2 hadm hX hp hp5
  | trialityD4 => exact normSylowAt_trialityD4 hr2 hadm hX hp hp5
  | PSp => exact normSylowAt_psp hXs hr2 hadm hX hp hp5
  | POmegaOdd => exact normSylowAt_pomega_of_lieModel hXs (Or.inl rfl) hr2 hadm hX hp hp5
  | POmegaPlus =>
      exact normSylowAt_pomega_of_lieModel hXs (Or.inr (Or.inl rfl)) hr2 hadm hX hp hp5
  | POmegaMinus =>
      exact normSylowAt_pomega_of_lieModel hXs (Or.inr (Or.inr rfl)) hr2 hadm hX hp hp5
  | F4 => exact normSylowAt_exceptional_of_lieModel hXs (Or.inl rfl) hr2 hadm hX hp hp5
  | E6 => exact normSylowAt_exceptional_of_lieModel hXs (Or.inr (Or.inl rfl)) hr2 hadm hX hp hp5
  | E7 =>
      exact normSylowAt_exceptional_of_lieModel hXs (Or.inr (Or.inr (Or.inl rfl))) hr2 hadm hX
        hp hp5
  | E8 =>
      exact normSylowAt_exceptional_of_lieModel hXs (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hr2
        hadm hX hp hp5
  | twistedE6 =>
      exact normSylowAt_exceptional_of_lieModel hXs (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hr2
        hadm hX hp hp5
  | twistedB2 => exact absurd hadm.2.2.2.1 hr2
  | twistedF4 => exact absurd hadm.2.2.2.1 hr2
  | Tits => exact absurd hadm.2.2.2.1 hr2

theorem fixesSylowOutside_of_lieModel
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {t : CFSG.Open.StatedLieTag} {n r f : ℕ} (ht : t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .twistedG2)
    (hr2 : r ≠ 2) (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hX : CFSG.Blueprint.LieModel X t n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    FixesSylowOutside X (inner X) p := by
  cases t with
  | PSL => exact absurd rfl ht.1
  | PSU => exact absurd rfl ht.2.1
  | twistedG2 => exact absurd rfl ht.2.2
  | PSp => exact fixesSylowOutside_psp hr2 hX hp hp5
  | POmegaOdd => exact fixesSylowOutside_pomega hXs (Or.inl rfl) hr2 hadm hX hp hp5
  | POmegaPlus => exact fixesSylowOutside_pomega hXs (Or.inr (Or.inl rfl)) hr2 hadm hX hp hp5
  | POmegaMinus => exact fixesSylowOutside_pomega hXs (Or.inr (Or.inr rfl)) hr2 hadm hX hp hp5
  | G2 => exact fixesSylowOutside_untwisted (Or.inl rfl) hr2 hadm hX hp hp5
  | F4 => exact fixesSylowOutside_untwisted (Or.inr (Or.inl rfl)) hr2 hadm hX hp hp5
  | E6 => exact fixesSylowOutside_untwisted (Or.inr (Or.inr (Or.inl rfl))) hr2 hadm hX hp hp5
  | E7 =>
      exact fixesSylowOutside_untwisted (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hr2 hadm hX
        hp hp5
  | E8 =>
      exact fixesSylowOutside_untwisted (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hr2 hadm hX
        hp hp5
  | twistedE6 => exact fixesSylowOutside_twistedE6 hr2 hadm hX hp hp5
  | trialityD4 => exact fixesSylowOutside_trialityD4 hr2 hadm hX hp hp5
  | twistedB2 => exact absurd hadm.2.2.2.1 hr2
  | twistedF4 => exact absurd hadm.2.2.2.1 hr2
  | Tits => exact absurd hadm.2.2.2.1 hr2

theorem autSylowTag_of_ne_twistedG2
    {t : CFSG.Open.StatedLieTag} (ht : t ≠ .twistedG2) :
    ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ∀ (n r f : ℕ), r ≠ 2 →
      CFSG.Open.StatedLieAdmissible t n r f → CFSG.Blueprint.LieModel X t n r f →
      ∀ p : ℕ, p.Prime → 5 ≤ p → AutSylowAt X p := by
  intro X _ _ hXs n r f hr2 hadm hX p hp hp5
  cases t with
  | PSL =>
      by_cases hn : n = 2
      · subst hn
        exact autSylowAt_psl_two hr2 hadm hX hp hp5
      · have hn3 : 3 ≤ n := by
          have h2 : 2 ≤ n := hadm.2.2.1
          omega
        obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
          CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
            hX
        let : Field K := hKfield
        have : Finite K := hKfin
        exact autSylowAt_of_mulEquiv e
          (autSylowAt_projectiveSL_of_three_le hadm.1 hr2 hadm.2.1 hKcard hn3 hp hp5)
  | PSU =>
      exact autSylowAt_of_statedPSU hr2
        (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)) hp hp5
  | twistedG2 => exact absurd rfl ht
  | PSp | POmegaOdd | POmegaPlus | POmegaMinus | G2 | F4 | E6 | E7 | E8 | twistedE6
    | trialityD4 | twistedB2 | twistedF4 | Tits =>
      exact autSylowAt_of_normSylowIn le_rfl
        (normSylowIn_inner_of_normSylowAt
          (normSylowAt_of_lieModel hXs ⟨by decide, by decide, by decide⟩ hr2 hadm hX hp hp5))
        (fixesSylowOutside_of_lieModel hXs ⟨by decide, by decide, by decide⟩ hr2 hadm hX hp hp5)

theorem kOddLieAutSylow_holds :
    KOddLieAutSylow := by
  intro X _ _ hXs t n r f hr2 hadm hX ht p hp hp5
  exact autSylowTag_of_ne_twistedG2 ht X hXs n r f hr2 hadm hX p hp hp5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
