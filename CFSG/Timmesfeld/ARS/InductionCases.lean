module

public import CFSG.Timmesfeld.ARS.Induction
public import CFSG.Timmesfeld.ARS.CaseHInput
public import CFSG.Timmesfeld.ARS.CaseHConnected
public import CFSG.Timmesfeld.ARS.CaseHU33

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Steinberg CFSG.Blueprint CFSG.Timmesfeld

theorem nonSimplyLacedOutcome_of_G2Frame {G : Type} [Group G] (hZ : Subgroup.center G = ⊥)
    {f : ℕ} (hf : 2 ≤ f) (hG : G2Frame G f) : NonSimplyLacedOutcome G := by
  obtain ⟨F, _, _, hF, φ, hc, hgen, hnt⟩ := hG
  have hq : 3 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨-, -, -, -, hmodel⟩ :=
    exists_lieModel_of_coneCompatible_G2 Nat.prime_two (by omega) hq hF hZ hc hgen hnt
  exact .inr (.inr (.inl ⟨f, hf, hmodel⟩))

theorem nonSimplyLacedOutcome_of_twistedD4Frame {G : Type} [Group G]
    (hZ : Subgroup.center G = ⊥) {f : ℕ} (hf : 1 ≤ f) (hG : TwistedD4Frame G f) :
    NonSimplyLacedOutcome G := by
  obtain ⟨F, _, _, hF, σ, hσ, φ, hc, hgen, hnt⟩ := hG
  obtain ⟨-, -, -, -, hmodel⟩ :=
    exists_lieModel_of_coneCompatible_twistedD4 Nat.prime_two hf hF σ hσ hZ hc hgen hnt
  exact .inr (.inr (.inr (.inl ⟨f, hf, .trialityD4, by decide, hmodel⟩)))

theorem caseHStep_of_frameInput (hF : CaseHFrameInput) : CaseHStep := by
  intro G _ R h _ A hA hmax hσ
  have hH : SigmaEqLambda R := sigmaEqLambda_of_mem h.root hA hσ
  refine Output.of_nonSimplyLaced ?_ (NSLData.of_sigmaEqLambda hH)
  have h3 := CaseH.three_le_ncard_linesThrough h hH hA hmax
  by_cases h23 : Nat.card A = 2 ∧ (linesThrough R A).ncard = 3
  · exact .inr (.inr (.inr (.inr (lieModel_PSU_of_caseH h hH hA h23.1 h23.2))))
  · have hT := CaseH.mTransitive_of_not_two_three h hH hA h3 h23
    rcases hF G R h hH hT A hA h3 h23 with ⟨f, hf, -, hG⟩ | ⟨f, hf, -, hG⟩
    · exact nonSimplyLacedOutcome_of_G2Frame h.center hf hG
    · exact nonSimplyLacedOutcome_of_twistedD4Frame h.center hf hG

end CFSG.Timmesfeld.ARS
