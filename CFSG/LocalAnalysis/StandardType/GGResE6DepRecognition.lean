module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLinear
public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGResE6DepSigned
public import CFSG.LocalAnalysis.StandardType.GGResE6DepUnitaryTwo
public import CFSG.LocalAnalysis.StandardType.GGResE6DepSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Certs


theorem GGResHyp.e6_marking_of_endpoint_facts
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (h5 : ∀ (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      3 ^ 5 ≤ Nat.card ↥(ggGamma X hN).range)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840) :
    GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with hX | hX
    · rw [hX]; exact hH.2.2.1.1
    · rw [hX]; exact hH.2.2.1.2 y K hH.2.2.2.2.1
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hInn
  have hMark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs X := by
    refine ⟨hperf, lab, hΛ, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F h =>
      ⟨h.1, h.2.1, h.2.2.choose, rfl, h.2.2.choose_spec⟩) hraw
  have marked (S : ℕ → LargeEvenLabel → Prop) (hs : S 3 lab) :
      GGInnerDiagOnLabel S 3 Bs X := GGInnerDiagOnLabel.mono_label
        (S := fun _ lab' => lab' = lab) (fun lab' heq => heq ▸ hs) hMark
  have hE : GGE6DepLabel lab := by
    obtain ⟨t, r, f⟩ := lab
    cases t
    case A =>
      change 1 ≤ f ∧ 1 ≤ r ∧ (r = 1 → 2 ≤ f) at hΛ
      rcases three_dvd_two_pow_pred_or_succ f with hminus | hplus
      · exact False.elim (GGResHyp.not_splitLinear_of_card_automizer_E6 hH hX hcard (marked _ ⟨rfl, hminus⟩))
      · by_cases hr : 5 ≤ r
        · by_cases hr5 : r = 5
          · exact False.elim (hH.not_relativeA5_of_card_automizer_E6 hX hcard
              (marked _ ⟨hr5, Or.inl ⟨rfl, hplus⟩⟩))
          · exact False.elim (GGResHyp.not_nonsplitClassical_of_card_automizer_E6 hH hX hcardBs hcard
              (marked _ ⟨hr, Or.inl ⟨rfl, hplus⟩⟩))
        · exact False.elim (GGResHyp.not_lowNonsplitClassical_of_gamma_ge_five hH hX h5
            (marked _ ⟨(show r ≤ 4 by omega), Or.inl ⟨rfl, hplus⟩⟩))
    case twA =>
      change 1 ≤ f ∧ 2 ≤ r ∧ (r = 2 → 2 ≤ f) at hΛ
      rcases three_dvd_two_pow_pred_or_succ f with hminus | hplus
      · by_cases hr : 5 ≤ r
        · by_cases hr5 : r = 5
          · exact False.elim (hH.not_relativeA5_of_card_automizer_E6 hX hcard
              (marked _ ⟨hr5, Or.inr ⟨rfl, hminus⟩⟩))
          · exact False.elim (GGResHyp.not_nonsplitClassical_of_card_automizer_E6 hH hX hcardBs hcard
              (marked _ ⟨hr, Or.inr ⟨rfl, hminus⟩⟩))
        · exact False.elim (GGResHyp.not_lowNonsplitClassical_of_gamma_ge_five hH hX h5
            (marked _ ⟨(show r ≤ 4 by omega), Or.inr ⟨rfl, hminus⟩⟩))
      · by_cases hd : 3 ∣ r + 1
        · by_cases hr : 5 ≤ r
          · by_cases hex : r = 5 ∧ f = 1
            · exact False.elim (GGResHyp.not_unitarySixTwo_of_card_automizer_E6 hH hX h5 hcard (marked _ (by
                obtain ⟨rfl, rfl⟩ := hex; rfl)))
            · exact False.elim (GGResHyp.not_splitUnitaryDvd_of_card_automizer_E6 hH hX hcardBs h5 hcard
                (marked _ ⟨rfl, hplus, hd, hr, hex⟩))
          · have hr2 : r = 2 := by
              have h2 : 2 ≤ r := hΛ.2.1
              omega
            have hf2 : 2 ≤ f := hΛ.2.2 hr2
            exact False.elim (GGResHyp.not_rankOneOrTwo_of_gamma_ge_five hH hX h5
              (marked _ (Or.inr ⟨hr2, hf2, Or.inr ⟨rfl, hplus⟩⟩)))
        · exact False.elim (GGResHyp.not_splitUnitaryCoprime_of_card_automizer_E6 hH hX hcardBs hcard (marked _ ⟨rfl, hplus, hd⟩))
    case B => exact False.elim (GGResHyp.not_symplectic_of_card_automizer_E6 hH hX hcardBs hcard (marked _ (Or.inl rfl)))
    case C => exact False.elim (GGResHyp.not_symplectic_of_card_automizer_E6 hH hX hcardBs hcard (marked _ (Or.inr rfl)))
    case D =>
      change 1 ≤ f ∧ 3 ≤ r at hΛ
      by_cases hr : 4 ≤ r
      · exact False.elim (GGResHyp.not_orthogonal_of_card_automizer_E6 hH hX hcardBs hcard (marked _ ⟨Or.inl rfl, hr⟩))
      · have hr3 : r = 3 := by have := hΛ.2; omega
        subst r
        have hMA : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, 3, f⟩) 3 Bs X := by
          refine ⟨hperf, ⟨.A, 3, f⟩, ⟨hΛ.1, by norm_num, by norm_num⟩, ?_⟩
          dsimp only [LargeEvenRawDatumLegacy] at hraw ⊢
          rw [if_pos rfl] at hraw
          obtain ⟨E, _, _, hE, hs, hna, θ, hN, hind⟩ := hraw
          exact ⟨E, inferInstance, inferInstance, hE, hs, hna, θ, rfl, hN, hind⟩
        rcases three_dvd_two_pow_pred_or_succ f with hminus | hplus
        · exact False.elim (GGResHyp.not_splitLinear_of_card_automizer_E6 hH hX hcard
            (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = ⟨.A, 3, f⟩)
              (fun lab heq => heq ▸ ⟨rfl, hminus⟩) hMA))
        · exact False.elim (GGResHyp.not_lowNonsplitClassical_of_gamma_ge_five hH hX h5
            (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = ⟨.A, 3, f⟩)
              (fun lab heq => heq ▸ ⟨by norm_num, Or.inl ⟨rfl, hplus⟩⟩) hMA))
    case twD =>
      change 1 ≤ f ∧ 2 ≤ r at hΛ
      by_cases hr : 4 ≤ r
      · exact False.elim (GGResHyp.not_orthogonal_of_card_automizer_E6 hH hX hcardBs hcard (marked _ ⟨Or.inr rfl, hr⟩))
      · have hr2 : r = 2 ∨ r = 3 := by have := hΛ.2; omega
        rcases hr2 with rfl | rfl
        · exact False.elim (GGResHyp.not_rankOneOrTwo_of_gamma_ge_five hH hX h5 (marked _ (Or.inl (Or.inr ⟨rfl, rfl⟩))))
        · have hMU : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 3, f⟩) 3 Bs X := by
            refine ⟨hperf, ⟨.twA, 3, f⟩, ⟨hΛ.1, by norm_num, by norm_num⟩, ?_⟩
            dsimp only [LargeEvenRawDatumLegacy] at hraw ⊢
            rw [if_neg (by norm_num : ¬ (3 = 2)), if_pos rfl] at hraw
            obtain ⟨E, _, _, hE, hs, hna, θ, hN, hind⟩ := hraw
            exact ⟨E, inferInstance, inferInstance, hE, hs, hna, θ, rfl, hN, hind⟩
          rcases three_dvd_two_pow_pred_or_succ f with hminus | hplus
          · exact False.elim (GGResHyp.not_lowNonsplitClassical_of_gamma_ge_five hH hX h5
              (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = ⟨.twA, 3, f⟩)
                (fun lab heq => heq ▸ ⟨by norm_num, Or.inr ⟨rfl, hminus⟩⟩) hMU))
          · exact False.elim (GGResHyp.not_splitUnitaryCoprime_of_card_automizer_E6 hH hX hcardBs hcard
              (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = ⟨.twA, 3, f⟩)
                (fun lab heq => heq ▸ ⟨rfl, hplus, by norm_num⟩) hMU))
    case E6 =>
      rcases three_dvd_two_pow_pred_or_succ f with hminus | hplus
      · exact Or.inl ⟨rfl, hminus⟩
      · exact False.elim (GGResHyp.not_oppositeE6_of_card_automizer_E6 hH hX hcard (marked _ (Or.inl ⟨rfl, hplus⟩)))
    case twE6 =>
      rcases three_dvd_two_pow_pred_or_succ f with hminus | hplus
      · exact False.elim (GGResHyp.not_oppositeE6_of_card_automizer_E6 hH hX hcard (marked _ (Or.inr ⟨rfl, hminus⟩)))
      · exact Or.inr ⟨rfl, hplus⟩
    case E7 => exact False.elim (GGResHyp.not_E7_E8_of_card_bstar hH hX hcardBs (marked _ (Or.inl rfl)))
    case E8 => exact False.elim (GGResHyp.not_E7_E8_of_card_bstar hH hX hcardBs (marked _ (Or.inr rfl)))
    case F4 => exact False.elim (GGResHyp.not_F4_of_card_automizer_E6 hH hX hcard (marked _ rfl))
    case G2 => exact False.elim (GGResHyp.not_smallLie hH hX (marked _ (Or.inl rfl)))
    case triD4 => exact False.elim (GGResHyp.not_smallLie hH hX (marked _ (Or.inr (Or.inl rfl))))
    case twB2 => exact False.elim (GGResHyp.not_smallLie hH hX (marked _ (Or.inr (Or.inr (Or.inl rfl)))))
    case twF4 =>
      exact False.elim (GGResHyp.not_smallLie hH hX (marked _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    case B2der =>
      exact False.elim (GGResHyp.not_smallLie hH hX (marked _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    case G2der =>
      exact False.elim (GGResHyp.not_smallLie hH hX
        (marked _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    case twF4der => exact False.elim (GGResHyp.not_smallLie hH hX (marked _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  exact marked _ hE

theorem GGResE6DepShape.e6_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    (hX : X = L ∨ X = K) :
    GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) p Bs X := by
  have hp3 : p = 3 := hS.1
  subst hp3
  have hcard : Nat.card (ggAutomizer X Bs) = 51840 := by
    rcases hX with hX | hX
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).1
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).2
  exact hH.e6_marking_of_endpoint_facts hX hS.2.1 (hS.five_le_card_range hX) hcard

end Certs

end CFSG.StandardType
