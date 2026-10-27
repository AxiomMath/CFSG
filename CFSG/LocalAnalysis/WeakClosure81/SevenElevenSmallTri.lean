module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriBundle
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriCentral
public import CFSG.LocalAnalysis.WeakClosure81.SevenNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

section Core


theorem seven_eleven_small (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle) (h77 : SevenSevenOddCentral G) (h772 : SevenSevenTwoInput G)
    (hIn : OrthReflParabolic) (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) :
    (∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ kSub V H E, u = k * v * k⁻¹) ∧
      SevenElevenAlt X (barSub (kSub V H E) φ V) := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hJK : pCoreOf 2 (kSub V H E) ≤ kSub V H E :=
    CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kSub V H E)
  refine ⟨exists_conj_dSet_of_card_eq_two h.toHyp73 h.transitive hJK hφ hS, ?_⟩
  have hSne : barSub (kSub V H E) φ V ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (⊥ : Subgroup X) = 1 := by simp
    rw [hbot, h1] at hS
    norm_num at hS
  obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  have hs : (s : X) ∈ barSub (kSub V H E) φ V := s.2
  have hsne : (s : X) ≠ 1 := fun hh => hs1 (Subtype.ext hh)
  obtain ⟨hord, hodd, hncl, hpc⟩ := seven_eleven_small_hyps h hφ hS hs hsne
  have hzs : Subgroup.zpowers (s : X) = barSub (kSub V H E) φ V :=
    seven_eleven_small_zpowers_eq hS hs hsne
  rcases fusionOddCore_le_center_or_isSymGp hCore h77 h hφ hS with hOZ | ⟨n, hn⟩
  · rcases hList.1 X (s : X) hord hodd hncl hpc hOZ with h4 | h5 | h6 | h9 | hsz | hTri
    · obtain ⟨m, n, hc⟩ := h4
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hS, m, n, ?_⟩)))
      rcases hc with ⟨hSp, htr⟩ | ⟨hU, htr⟩ | hOrth | hWr
      · exact Or.inl ⟨hSp, fun t ht ht1 => by
          have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
          rw [hts]
          exact htr⟩
      · exact Or.inr (Or.inl ⟨hU, fun t ht ht1 => by
          have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
          rw [hts]
          exact htr⟩)
      · exact Or.inr (Or.inr (Or.inl hOrth))
      · exact Or.inr (Or.inr (Or.inr hWr))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hS, h5⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hS, h6⟩))))
    · obtain ⟨L, hsL, hL⟩ := h9
      exfalso
      exact seven_nine_in hIn h.toHyp73 hφ (by simpa only [hzs] using Subgroup.zpowers_le.mpr hsL)
        (by simpa only [hzs] using hL)
    · obtain ⟨n', hn', hsz'⟩ := hsz
      exact absurd hsz' (h772 V H E h X φ hφ hS hOZ n' hn')
    · exact absurd hTri <|
        SevenElevenTri.not_isTrialityOddTransp_quotient hList.2.1 hList.2.2 h hφ hS hs hsne
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hS, n, hn⟩))))

end Core

end CFSG.LocalAnalysis.WeakClosure81
