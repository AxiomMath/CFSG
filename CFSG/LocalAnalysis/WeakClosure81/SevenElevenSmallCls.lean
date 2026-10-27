module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriBundle
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriCentral
public import CFSG.LocalAnalysis.WeakClosure81.SevenNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def OddTranspositionCoreInputSCCls : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    ¬ fusionOddCore X ≤ Subgroup.center X →
    (∃ n : ℕ, IsSymTransposition X n s) ∨
      (∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ Lh ∧
        ¬ Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ pCoreOf 2 Lh ∧
        (⨆ (y : X ⧸ fusionOddCore X)
            (_ : conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y ≤ Lh),
            conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y) = Lh ∧
        HasQuotShape Lh (pCoreOf 2 Lh : Set (X ⧸ fusionOddCore X)) (fun Y _ => IsSymGp Y 3) ∧
        4 ≤ Set.ncard {W : Subgroup (X ⧸ fusionOddCore X) | ∃ x ∈ pCoreOf 2 Lh,
            W = conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) x}) ∨
      ∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        ∃ hsLh : QuotientGroup.mk' (fusionOddCore X) s ∈ Lh,
        Subgroup.normalClosure ({⟨_, hsLh⟩} : Set ↥Lh) = ⊤ ∧
        ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥Lh ⧸ fusionZStar ↥Lh) n

theorem OddTranspositionCoreInputSCCls.toInput (h : OddTranspositionCoreInputSCCls) :
    OddTranspositionCoreInputSC := by
  intro X _ _ s hord hodd hncl hpc hOZ
  rcases h X s hord hodd hncl hpc hOZ with ⟨n, hn⟩ | h2 | h3
  · exact Or.inl ⟨n, isSymGp_of_isSymTransposition hn⟩
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

@[expose] def SevenElevenSmallAltCls (X : Type) [Group X] (S : Subgroup X) : Prop :=
  Nat.card S = 2 ∧
    ((∃ m n : ℕ,
      (IsSpGp (X ⧸ Subgroup.center X) m n ∧ ∀ s ∈ S, s ≠ 1 → IsSymplecticTransvection X m n s) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ ∀ s ∈ S, s ≠ 1 → IsUnitaryTransvection X m n s) ∨
      (∀ s ∈ S, s ≠ 1 → IsOrthReflection X m n s) ∨
      (∀ s ∈ S, s ≠ 1 → IsWreathTransposition X n m s)) ∨
      (∃ n : ℕ, ∀ s ∈ S, s ≠ 1 → IsSymTransposition X n s) ∨
      (∀ s ∈ S, s ≠ 1 → IsOrth63Reflection X s))

section Core

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem fusionOddCore_le_center_or_isSymTransposition (hCore : OddTranspositionCoreInputSCCls)
    (h77 : SevenSevenOddCentral G) (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) :
    fusionOddCore X ≤ Subgroup.center X ∨
      ∃ n : ℕ, ∀ s ∈ barSub (kSub V H E) φ V, s ≠ 1 → IsSymTransposition X n s := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  by_cases hOZ : fusionOddCore X ≤ Subgroup.center X
  · exact Or.inl hOZ
  · right
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
    rcases hCore X (s : X) hord hodd hncl hpc hOZ with ⟨n, hn⟩ | h78 | hsub
    · refine ⟨n, fun t ht ht1 => ?_⟩
      have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
      rw [hts]
      exact hn
    · obtain ⟨L, hle, hgen, hquot, hfour⟩ := oddCoreLiftFischer X (s : X) hord hodd h78
      have hc : SevenEightBarConfig (barSub (kSub V H E) φ V) L :=
        ⟨by rw [← hzs]; exact hle, by rw [← hzs]; exact hgen, hquot,
          by rw [← hzs]; exact hfour⟩
      exact absurd (fusionOddCore_le_center_of_sevenEightBarConfig h hφ hc) hOZ
    · obtain ⟨L, hsL, hcl, n, hn, hL, hLnot⟩ := oddCoreLiftL2SzSC X (s : X) hord hncl hOZ hsub
      have hVle : barSub (kSub V H E) φ V ≤ L.subtype.range := by
        rw [Subgroup.range_subtype]
        simpa only [hzs] using Subgroup.zpowers_le.mpr hsL
      have hone : ∀ y : ↥L, L.subtype y ∈ barSub (kSub V H E) φ V → y ≠ 1 →
          Subgroup.normalClosure ({y} : Set ↥L) = ⊤ := by
        intro y hy hy1
        have hy1' : (y : X) ≠ 1 := fun hh => hy1 (Subtype.ext hh)
        have hys : (y : X) = s := seven_eleven_small_eq_of_mem hS hs hsne hy hy1'
        have : y = ⟨s, hsL⟩ := Subtype.ext hys
        rw [this]
        exact hcl
      exact absurd (h77 V H E h X φ hφ hS ↥L L.subtype L.subtype_injective hVle hone n hn hL)
        hLnot

theorem seven_eleven_small_cls (hCore : OddTranspositionCoreInputSCCls)
    (hList : OddTranspListBundleCls) (h77 : SevenSevenOddCentral G)
    (h772 : SevenSevenTwoInput G) (hIn : OrthReflParabolic) (h : Hyp711 V H E) {X : Type}
    [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) :
    (∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ kSub V H E, u = k * v * k⁻¹) ∧
      SevenElevenSmallAltCls X (barSub (kSub V H E) φ V) := by
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
  refine ⟨hS, ?_⟩
  rcases fusionOddCore_le_center_or_isSymTransposition hCore h77 h hφ hS with hOZ | ⟨n, hn⟩
  · have hAlt : OddTranspListAlt X (s : X) := by
      rcases hList.1 X (s : X) hord hodd hncl hpc hOZ with hAlt | hTri
      · exact hAlt
      · exact absurd hTri <|
          SevenElevenTri.not_isTrialityOddTransp_quotient hList.2.1 hList.2.2 h hφ hS hs hsne
    rcases hAlt with h4 | h5 | h6 | h9 | hsz
    · obtain ⟨m, n, hc⟩ := h4
      refine Or.inl ⟨m, n, ?_⟩
      rcases hc with ⟨hSp, htr⟩ | ⟨hU, htr⟩ | hOrth | hWr
      · exact Or.inl ⟨hSp, fun t ht ht1 => by
          have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
          rw [hts]
          exact htr⟩
      · exact Or.inr (Or.inl ⟨hU, fun t ht ht1 => by
          have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
          rw [hts]
          exact htr⟩)
      · exact Or.inr (Or.inr (Or.inl (fun t ht ht1 => by
          have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
          rw [hts]
          exact hOrth)))
      · exact Or.inr (Or.inr (Or.inr (fun t ht ht1 => by
          have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
          rw [hts]
          exact hWr)))
    · obtain ⟨k, hk⟩ := h5
      refine Or.inr (Or.inl ⟨k, fun t ht ht1 => ?_⟩)
      have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
      rw [hts]
      exact hk
    · refine Or.inr (Or.inr (fun t ht ht1 => ?_))
      have hts : t = (s : X) := seven_eleven_small_eq_of_mem hS hs hsne ht ht1
      rw [hts]
      exact h6
    · obtain ⟨L, hsL, hL⟩ := h9
      exfalso
      exact seven_nine_in hIn h.toHyp73 hφ (by simpa only [hzs] using Subgroup.zpowers_le.mpr hsL)
        (by simpa only [hzs] using hL)
    · obtain ⟨n', hn', hsz'⟩ := hsz
      exact absurd hsz' (h772 V H E h X φ hφ hS hOZ n' hn')
  · exact Or.inr (Or.inl ⟨n, hn⟩)

end Core

end CFSG.LocalAnalysis.WeakClosure81
