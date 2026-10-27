module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.Models
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import Certificates.Certificate18000

import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcLargeRee
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.StronglyEmbedded.Catalog.Suzuki

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open


theorem blueprintLieModel_of_models_of_ne_tits {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hm : CFSG.Models.LieModel X t n p f) (ht : t ≠ .Tits) :
    CFSG.Blueprint.LieModel X t n p f := by
  obtain ⟨hadm, hcl | ⟨h0, ⟨idx, hv⟩, hnames, ⟨e⟩⟩⟩ := hm
  · refine Or.inl ⟨?_, hcl⟩
    cases t <;> first | decide | exact hcl.2.elim
  · subst h0
    cases t
    all_goals first
      | (exfalso; cases idx <;> simp only [CFSG.Models.NamesTag] at hnames; done)
      | skip
    case G2 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
          (c := TauCeti.LieTypeIndex.G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 e⟩)
    case F4 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
          (c := TauCeti.LieTypeIndex.F4) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 e⟩)
    case E6 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
          (c := TauCeti.LieTypeIndex.E6) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 e⟩)
    case E7 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
          (c := TauCeti.LieTypeIndex.E7) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 e⟩)
    case E8 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
          (c := TauCeti.LieTypeIndex.E8) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 e⟩)
    case twistedE6 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm,
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.twistedChevalleyModel_of_bridge
          (t := .E6) (c := TauCeti.LieTypeIndex.twistedE6)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 e⟩)
    case trialityD4 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm,
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.twistedChevalleyModel_of_bridge
          (t := .D4) (c := TauCeti.LieTypeIndex.trialityD4)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 e⟩)
    case twistedB2 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i m
      obtain ⟨rfl, rfl⟩ := hnames
      obtain ⟨K, _, _, _, hK⟩ :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.exists_field_card 2 (2 * m + 1)
          Nat.prime_two (by omega)
      have e₂ : TauCeti.ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩ ≃*
          CFSG.Blueprint.suzukiGroup m K :=
        (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).trans
          (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).symm
      have h3 : 3 ≤ 2 * m + 1 := hadm.2.2.2.2.2
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, m, by omega, K, inferInstance, inferInstance,
        rfl, hK, ⟨e.trans e₂⟩⟩))
    case twistedG2 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i m
      obtain ⟨rfl, rfl⟩ := hnames
      obtain ⟨K, _, _, _, hK⟩ :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.exists_field_card 3 (2 * m + 1)
          Nat.prime_three (by omega)
      obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv K hK
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, m, rfl, K, inferInstance,
        inferInstance, hK, ⟨e.trans b.symm⟩⟩⟩))
    case twistedF4 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i m
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide,
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.reeTitsModel_reeF4_of_equiv hadm e⟩))
    case Tits =>
      exact absurd rfl ht

theorem isCalL0_of_lieModel_two {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (hm : CFSG.Models.LieModel X t n 2 f)
    (h : 3 ≤ f ∨ t = .trialityD4 ∨
      f = 2 ∧ (t = .PSU ∧ (n = 4 ∨ n = 5) ∨ t = .POmegaMinus ∧ n = 4)) :
    IsCalL0 X := by
  have ht : t ≠ .Tits := by
    rintro rfl
    have hf : f = 1 := hm.1.2.2.2.2
    rcases h with h3 | hD4 | ⟨h2, -⟩
    · omega
    · exact absurd hD4 (by decide)
    · omega
  have hlm := blueprintLieModel_of_models_of_ne_tits hm ht
  rcases h with h3 | hD4 | ⟨hf2, hrest⟩
  · exact Or.inl ⟨f, by omega, t, n, hlm⟩
  · subst hD4
    have hn0 : n = 0 := hm.1.2.2
    rw [hn0] at hlm
    rcases Nat.lt_or_ge f 3 with hf3 | hf3
    · have h12 : f = 1 ∨ f = 2 := by
        have h1 : 1 ≤ f := hm.1.2.1
        omega
      rcases h12 with rfl | rfl
      · exact Or.inr (Or.inl hlm)
      · exact Or.inr (Or.inr (Or.inl hlm))
    · exact Or.inl ⟨f, by omega, .trialityD4, 0, hlm⟩
  · subst hf2
    rcases hrest with ⟨hPSU, hn45⟩ | ⟨hPOm, hn4⟩
    · subst hPSU
      rcases hn45 with hn4 | hn5
      · subst hn4
        exact Or.inr (Or.inr (Or.inr (Or.inl hlm)))
      · subst hn5
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlm))))
    · subst hPOm
      subst hn4
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlm)))))

end CFSG.LocalAnalysis.WeakClosure81
