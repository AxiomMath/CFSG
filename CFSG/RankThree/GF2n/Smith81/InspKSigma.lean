module

public import CFSG.Timmesfeld.ARS.CaseHFinal
public import CFSG.Timmesfeld.ARS.Induction
public import CFSG.Timmesfeld.ARS.CaseHConnected

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Orders
  CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix

section CertBound


theorem KFact.exists_lieModel_of_sigmaEqLambda {G : Type} [Group G] {R : Set (Subgroup G)}
    (h : ARS.Hyp G R) (hS : SigmaEqLambda R) (hcard : ∀ A ∈ R, Nat.card A ≠ 2) :
    (∃ n f, LieModel G .PSL n 2 f) ∨ (∃ f, LieModel G .G2 0 2 f) ∨
      (∃ f, LieModel G .trialityD4 0 2 f) := by
  classical
  have := h.finite
  obtain ⟨A, hA, -⟩ := h.nondeg
  by_cases hmax : IsCoatom (Subgroup.normalizer (A : Set G))
  · have h3 := CaseH.three_le_ncard_linesThrough h hS hA hmax
    have h23 : ¬ (Nat.card A = 2 ∧ (linesThrough R A).ncard = 3) := fun h' => hcard A hA h'.1
    have hT := CaseH.mTransitive_of_not_two_three h hS hA h3 h23
    rcases caseHFrameInput G R h hS hT A hA h3 h23 with ⟨f, hf, -, hG⟩ | ⟨f, hf, -, hG⟩
    · obtain ⟨F, _, _, hF, φ, hc, hgen, hnt⟩ := hG
      have hq : 3 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
      obtain ⟨-, -, -, -, hmodel⟩ :=
        exists_lieModel_of_coneCompatible_G2 Nat.prime_two (by omega) hq hF h.center hc hgen hnt
      exact Or.inr (Or.inl ⟨f, hmodel⟩)
    · obtain ⟨F, _, _, hF, σ, hσ', φ, hc, hgen, hnt⟩ := hG
      obtain ⟨-, -, -, -, hmodel⟩ :=
        exists_lieModel_of_coneCompatible_twistedD4 Nat.prime_two hf hF σ hσ' h.center hc hgen hnt
      exact Or.inr (Or.inr ⟨f, hmodel⟩)
  · obtain ⟨Δ, hΔ, hAΔ⟩ := (exists_isTI_iff h hA).1 hmax
    have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
      fun _ hA _ hB e => eq_of_omegaSet_eq h hA hB e
    obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow h.root h.noIsolated h.nondeg hΩ hΔ.isWeakTI hAΔ
    obtain ⟨hm2, X, hX⟩ := Linear.exists_isRootFrame h.root h.noIsolated h.nondeg hΩ hΔ hAΔ hm
    have hconf := hX.isConfig
    have hgen := hX.iSup_adj_eq_top
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨f, -, -, hL⟩ := hconf.lieModel_A_two h.root h.noIsolated h.center hgen
      exact Or.inl ⟨3, f, hL⟩
    · obtain ⟨f, -, -, hL⟩ := hconf.lieModel_A h.root h.noIsolated h.center hm3 hgen
      exact Or.inl ⟨m + 1, f, hL⟩

end CertBound

end CFSG.RankThree.GF2n.Smith81.Insp
