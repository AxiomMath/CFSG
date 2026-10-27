module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalG2Four
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairProof
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Model
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeStep
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTits
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Model
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Step
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Model
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6Step
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedStep
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Model
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Sec810Proof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoC
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatNormal
public import CFSG.StandardComponent.AschbacherSeitz.ClassicalNF

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (standardComponentOddCore)
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoL3Even
open CFSG.StandardComponent.AschbacherSeitz

theorem hyp31_of_excNF {G : Type} [Group G] [Finite G] {A : Subgroup G} (hII : ExcHypII)
    (hH : RankTwoHypNF G A) (hO : standardComponentOddCore G = ⊥)
    (hT : RankTwoExceptionalEvenType (rankTwoQuot A)) : AS76b.Hyp31 A :=
  ⟨hH.standard, hII _ hH.standard.1.1 hT, hO, lt_of_lt_of_le one_lt_two hH.rank, hH.not_normal⟩

theorem false_of_classicalNF
    (h6 : ∀ (H : Type) [Group H] [Finite H] (B : Subgroup H), RankTwoHypNF H B →
      standardComponentOddCore H = ⊥ → ¬ RankTwoClassicalEvenType (rankTwoQuot B))
    {H : Type} [Group H] [Finite H] {B : Subgroup H} (hB : RankTwoHypNF H B)
    (hO : standardComponentOddCore H = ⊥)
    (hT : (∃ n m : ℕ, 4 ≤ n ∧ StatedClassicalModel (rankTwoQuot B) .PSL n 2 m) ∨
      (∃ n m : ℕ, 4 ≤ n ∧ StatedClassicalModel (rankTwoQuot B) .PSU n 2 m) ∨
      (∃ n m : ℕ, 2 ≤ n ∧ StatedClassicalModel (rankTwoQuot B) .PSp n 2 m) ∨
      ∃ n m : ℕ, 4 ≤ n ∧ (StatedClassicalModel (rankTwoQuot B) .POmegaPlus n 2 m ∨
        StatedClassicalModel (rankTwoQuot B) .POmegaMinus n 2 m))
    (h7 : 2 ^ 7 ∣ Nat.card (rankTwoQuot B)) : False :=
  h6 H B hB hO ⟨hT, not_alternating_of_two_pow_seven_dvd h7⟩

theorem g2Four_of_configNF (h75 : AS76b.Asc75Theorem4) (h32 : AS76b.Lemma32)
    (hSuz : SuzL34DiagInput)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hH : RankTwoHypNF G A)
    (hO : standardComponentOddCore G = ⊥) (hA : AS76b.Hyp31 A) (D : ExcModel A) {g : G}
    {R T Q : Subgroup G} (hc : Config814 D g R T Q)
    (ih : AS81.Sec3Below (Nat.card G)) :
    ChevalleyExceptionalModel (rankTwoQuot A) .G2 2 2 := by
  have h2 : ∀ (H : Type) [Group H] [Finite H] (B : Subgroup H), RankTwoHypNF H B →
      standardComponentOddCore H = ⊥ → RankTwoBenderType (rankTwoQuot B) →
        SuzukiModel (rankTwoQuot B) 2 3 ∧ NativeSporadic.IsSporadic (rankTwoX B) .Ru := by
    intro H _ _ B hHB hOB hTB
    exact rankTwoBenderStandardNF H B hHB hOB hTB
  have h6 : ∀ (H : Type) [Group H] [Finite H] (B : Subgroup H), RankTwoHypNF H B →
      standardComponentOddCore H = ⊥ → ¬ RankTwoClassicalEvenType (rankTwoQuot B) := by
    intro H _ _ B hHB hOB hTB
    exact rankTwoClassicalEvenStandardNF H B hHB hOB hTB
  have h4 : ∀ (H : Type) [Group H] [Finite H] (B : Subgroup H), RankTwoHypNF H B →
      ∀ m : ℕ, 2 ≤ m → StatedClassicalModel (rankTwoQuot B) .PSL 3 2 m →
        (standardComponentOddCore H = ⊥ → m = 2) ∧
        (m = 2 →
          (NativeSporadic.IsSporadic (rankTwoX B ⧸ Subgroup.center (rankTwoX B)) .Suz ∧
              Nat.card (Subgroup.center (rankTwoX B)) ∣ 3) ∨
            (Nonempty (Subgroup.center B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
              NativeSporadic.IsSporadic (rankTwoX B) .He)) ∧
        (standardComponentOddCore H = ⊥ →
          NativeSporadic.IsSporadic (rankTwoX B) .Suz ∨
            (Nonempty (Subgroup.center B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
              NativeSporadic.IsSporadic (rankTwoX B) .He)) := by
    intro H _ _ B hHB m hm hM
    exact rankTwoL3EvenStandardNF H B hHB m hm hM
  obtain ⟨hstd, hnn⟩ := standard_of_config h75 h32 hA hc
  have hLAW : AS76b.layerCentralizer A Q ≤ A ⊓ centralizer (Q : Set G) :=
    AS76b.layerCentralizer_le A Q
  have hLW : AS76b.layerCentralizer A Q ≤ centralizer (Q : Set G) := hLAW.trans inf_le_right
  have hLA : AS76b.layerCentralizer A Q ≤ A := hLAW.trans inf_le_left
  have hH' : RankTwoHypNF ↥(centralizer (Q : Set G))
      ((AS76b.layerCentralizer A Q).subgroupOf (centralizer (Q : Set G))) :=
    ⟨hstd, hnn, two_le_pRank_centralizer_subgroupOf hc.le hLA hH.rank⟩
  have hWlt := AS81.card_centralizer_lt_of_rankTwoHypNF hH hO hc.ne_bot
  obtain ⟨B, hB', hO', ⟨f⟩⟩ := CFSG.ComponentClassification.RankTwoClassical.exists_rankTwoHypNF_quotient hH'
  have hBlt : Nat.card (↥(centralizer (Q : Set G)) ⧸
      standardComponentOddCore ↥(centralizer (Q : Set G))) < Nat.card G :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)) hWlt
  let eB : rankTwoQuot B ≃* rankTwoQuot (AS76b.layerCentralizer A Q) :=
    f.symm.trans (quotCenterCongr (subgroupOfEquivOfLe hLW))
  have hR := hc.sylowR
  have hQA := hc.le
  have hZL := hc.odd_center
  have hlevi := hc.levi
  have hq := hc.two_lt_q
  have hdiag := hc.diag
  clear hc
  cases D with
  | g2 m hm K hK e =>
    by_cases hm2 : m = 2
    · subst hm2
      exact ⟨⟨Nat.prime_two, by norm_num, rfl, by norm_num⟩, K, inferInstance, inferInstance, hK,
        ⟨e⟩⟩
    · simp only [ExcModel.LeviType, hm2, ite_false] at hlevi
      exact (false_of_benderNF h2 hB' hO' (by omega)
        (SectionRank.statedClassicalModel_of_mulEquiv eB hlevi)).elim
  | f4 m hm K hK e =>
    simp only [ExcModel.LeviType] at hlevi
    have hT := SectionRank.statedClassicalModel_of_mulEquiv eB hlevi
    exact (false_of_classicalNF h6 hB' hO' (Or.inr (Or.inr (Or.inl ⟨3, m, by norm_num, hT⟩)))
      (two_pow_seven_dvd_of_classical hm (by decide) (by decide) hT)).elim
  | e6 m hm K hK e =>
    simp only [ExcModel.LeviType] at hlevi
    have hT := SectionRank.statedClassicalModel_of_mulEquiv eB hlevi
    exact (false_of_classicalNF h6 hB' hO' (Or.inl ⟨6, m, by norm_num, hT⟩)
      (two_pow_seven_dvd_of_classical hm (by decide) (by decide) hT)).elim
  | e7 m hm K hK e =>
    simp only [ExcModel.LeviType] at hlevi
    have hT := SectionRank.statedClassicalModel_of_mulEquiv eB hlevi
    exact (false_of_classicalNF h6 hB' hO'
      (Or.inr (Or.inr (Or.inr ⟨6, m, by norm_num, Or.inl hT⟩)))
      (two_pow_seven_dvd_of_classical hm (by decide) (by decide) hT)).elim
  | e8 m hm K hK e =>
    simp only [ExcModel.LeviType] at hlevi
    have hT := SectionRank.chevalleyExceptionalModel_of_mulEquiv eB hlevi
    have hType : RankTwoExceptionalEvenType (rankTwoQuot B) :=
      Or.inr (Or.inl ⟨.E7, by decide, m, hm, hT⟩)
    obtain ⟨hG2, -⟩ := (ih _ B hBlt).2 hB' hO' hType
    exact (false_of_g2Four_of_e7 hm hG2 hT).elim
  | triality m hm K hK σ hσ e =>
    simp only [ExcModel.LeviType] at hlevi
    rcases hlevi with hL3 | hL2
    · have hT := SectionRank.statedClassicalModel_of_mulEquiv eB hL3
      have hm2 : 2 ≤ m := by
        simp only [ExcModel.q] at hq
        by_contra h
        interval_cases m
        norm_num at hq
      have hm' : m = 2 := ((ih _ B hBlt).1 hB' m hm2 hT).1 hO'
      subst hm'
      exact (false_of_triality_fourNF hSuz h32 h4 hA hH hR hQA hstd hnn hZL hL3
        (hdiag rfl hL3)).elim
    · exact (false_of_benderNF h2 hB' hO' (by omega)
        (SectionRank.statedClassicalModel_of_mulEquiv eB hL2)).elim
  | twistedE6 m hm K hK σ hσ e =>
    simp only [ExcModel.LeviType] at hlevi
    rcases hlevi with hU | hO8
    · have hT := SectionRank.statedClassicalModel_of_mulEquiv eB hU
      exact (false_of_classicalNF h6 hB' hO' (Or.inr (Or.inl ⟨6, m, by norm_num, hT⟩))
        (two_pow_seven_dvd_of_classical hm (by decide) (by decide) hT)).elim
    · have hT := SectionRank.statedClassicalModel_of_mulEquiv eB hO8
      exact (false_of_classicalNF h6 hB' hO'
        (Or.inr (Or.inr (Or.inr ⟨4, m, le_rfl, Or.inr hT⟩)))
        (two_pow_seven_dvd_of_classical hm (by decide) (by decide) hT)).elim
  | ree a ha K hK e =>
    simp only [ExcModel.LeviType] at hlevi
    exact (false_of_benderNF h2 hB' hO' (by omega)
      (SectionRank.statedClassicalModel_of_mulEquiv eB hlevi)).elim
  | tits K hK e =>
    exact hlevi.elim

theorem step814_of_open (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    (h4 : AS76b.Asc75Theorem4) (h810 : E7Sec8.E7Sec810) : ∀ t, Step814 t := by
  intro t
  cases t
  case G2 => exact step814_g2_model h4 h32 h33
  case F4 => exact F4Sec8.step814_f4 h32 h33 h4
  case E6 => exact E6Sec8.step814_e6 h32 h33 h4
  case E7 => exact E7Sec8.step814_e7 h32 h4 h810
  case E8 => exact E8.step814_e8 h32 h33 h4
  case twistedE6 => exact TwistedE6Sec8.step814_twistedE6 h32 h33 h4
  case trialityD4 => exact D4.step814_trialityD4 h32 h33 h4
  case twistedF4 => exact ReeSec8.step814_ree h32 h33 h4
  case Tits => exact step814_tits h32 h33 h4
  all_goals
    intro G _ _ A D hD
    cases D <;> cases hD

theorem excAt_of_belowNF {G : Type} [Group G] [Finite G] (hII : ExcHypII)
    (h75 : AS76b.Asc75Theorem4) (h32 : AS76b.Lemma32) (h83 : Step83)
    (h814 : ∀ t, Step814 t) (hZ : G2FourOddCenter) (hSuz : SuzL34DiagInput)
    (h81 : StepAS81TwoB)
    (hP : ∀ (X : Type) [Group X] [Finite X] (t : X)
      (h : LargeExtraspecial.S14.PattersonCo1Hyp X t), Sporadic.Co1Patterson.NotWeaklyClosed h →
        HoltFree.Co1TwoBData X t → Nonempty (X ≃* Blueprint.NativeSporadic.Co1))
    (A : Subgroup G) (ih : AS81.Sec3Below (Nat.card G)) :
    RankTwoHypNF G A → standardComponentOddCore G = ⊥ →
      RankTwoExceptionalEvenType (rankTwoQuot A) →
        ChevalleyExceptionalModel A .G2 2 2 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Co1 := by
  intro hH hO hT
  have hA := hyp31_of_excNF hII hH hO hT
  have hZA := h83 G A hA hT
  obtain ⟨D⟩ := nonempty_excModel hT
  obtain ⟨g, R, T, Q, hc⟩ := h814 D.tag G A D rfl hA hZA
  have hG2Q := g2Four_of_configNF h75 h32 hSuz hH hO hA D hc ih
  have hZ1 : center ↥A = ⊥ := hZ _ hH.standard.1.1 hG2Q hZA
  let e : ↥A ≃* rankTwoQuot A :=
    ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm
  have hG2 : ChevalleyExceptionalModel A .G2 2 2 :=
    SectionRank.chevalleyExceptionalModel_of_mulEquiv e hG2Q
  obtain ⟨z, hz, hw, hB⟩ := h81 G A hH hO hG2 ih
  exact ⟨hG2, hP _ z hz hw hB⟩

theorem rankTwoExceptionalEvenStandardNF :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      standardComponentOddCore G = ⊥ → RankTwoExceptionalEvenType (rankTwoQuot A) →
        ChevalleyExceptionalModel A .G2 2 2 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Co1 := by
  have h32 := RankTwoFoundation.lemma32
  have h33 := RankTwoFoundation.lemma33Three
  have h4 := RankTwoFoundation.asc75Theorem4
  have h810 := E7Sec8.e7Sec810 h32 h33 h4
  have h17 := AS81.step17G24Odd h4 AS76b.asc08Lemma34
  have hSN := AS81.sec3SHatNormal_of h17
  have hFG := AS81.sec3CentZNormalizes_of_sec3SHatNormal h17 hSN
  have h2C := HoltFree.co1TwoCControl
  have hII := RankTwoExcHypII.excHypII RankTwoExcHypII.twistedE6TwoEvenHypII
  have h83 := step83_of h32 h33 excPairCent
  have h814 := step814_of_open h32 h33 h4 h810
  have h81 := AS81.stepAS81_of_open AS81.l34GeneralNF hFG h2C
  have hP : ∀ (X : Type) [Group X] [Finite X] (t : X)
      (h : LargeExtraspecial.S14.PattersonCo1Hyp X t), Sporadic.Co1Patterson.NotWeaklyClosed h →
        HoltFree.Co1TwoBData X t → Nonempty (X ≃* Blueprint.NativeSporadic.Co1) :=
    fun _ _ _ _ h hw hB => HoltFree.co1_of_notWeaklyClosed_holtFree h2C h hw hB
  suffices h : ∀ (N : ℕ) (G : Type) [Group G] [Finite G] (A : Subgroup G), Nat.card G = N →
      RankTwoHypNF G A → standardComponentOddCore G = ⊥ →
        RankTwoExceptionalEvenType (rankTwoQuot A) →
          ChevalleyExceptionalModel A .G2 2 2 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Co1 by
    intro G _ _ A hH hO hT
    exact h (Nat.card G) G A rfl hH hO hT
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro G _ _ A hN hH hO hT
    have hBelow : AS81.Sec3Below (Nat.card G) := by
      intro G' _ _ A' hlt
      refine ⟨?_, ?_⟩
      · intro hH' m hm hM
        exact rankTwoL3EvenStandardNF G' A' hH' m hm hM
      · intro hH' hO' hT'
        exact ih (Nat.card G') (by omega) G' A' rfl hH' hO' hT'
    exact excAt_of_belowNF hII h4 h32 h83 h814 g2FourOddCenter suzL34DiagInput h81 hP A
      hBelow hH hO hT

theorem rankTwoExceptionalEvenStandard_of_open (hBender : RankTwoBenderStandard)
    (hL3 : RankTwoL3EvenStandard) (h6 : RankTwoClassicalEvenStandard) :
    RankTwoExceptionalEvenStandard := by
  intro G _ _ A hH hO hT
  exact rankTwoExceptionalEvenStandardNF (G := G) (A := A) hH.toNF hO hT

end CFSG.ComponentClassification.RankTwoExceptional
