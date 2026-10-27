module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeylTypes
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

section Frames

@[expose] def GGSixBstarExcFrameOn (τ : Tag) (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    (∃ ι : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ ggM p B x L D J, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
        ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s))) ∨
    ∀ g ∈ ggM p B x L D J, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
      g ∈ Subgroup.centralizer (Bs : Set G)

theorem ggNoOffender_of_excFrameOn {τ : Tag} {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixBstarExcFrameOn τ P)
    (hW : ∀ t n f p, P t n f p → p.Prime → p ≠ 2 → GGWeylNoOffender τ p) :
    GGSixBstarNoOffenderOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rcases h G p B Bs x L D J t n f ψ hP hctx hC with ⟨ι, hinj, hrange, hact⟩ | hcent
  · refine NoOffExc.noOffender_of_modelAct (TableBExc.torusPerm τ p)
      (NoOffExc.torusPerm_injective hp2) (fun A hA hA1 => ?_) hinj hrange hact
    have h1 := hW t n f p hP hp hp2 A hA hA1
    rw [Nat.card_eq_fintype_card (α := Fin τ.rank → ZMod p), Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    exact h1
  · exact NoOffExc.noOffender_of_centralize hcent

theorem ggSixBstarNoOffenderAt_of_on₃ {P Q R : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (t : StatedLieTag) (hP : GGSixBstarNoOffenderOn P) (hQ : GGSixBstarNoOffenderOn Q)
    (hR : GGSixBstarNoOffenderOn R) (hPQR : ∀ n f p, P t n f p ∨ Q t n f p ∨ R t n f p) :
    GGSixBstarNoOffenderAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx hC
  rcases hPQR n f p with h | h | h
  · exact hP G p B Bs x L D J t n f ψ h hctx hC
  · exact hQ G p B Bs x L D J t n f ψ h hctx hC
  · exact hR G p B Bs x L D J t n f ψ h hctx hC

@[expose] def GGExcF4Label (t : StatedLieTag) (_n _f _p : ℕ) : Prop :=
  t = .F4

@[expose] def GGExcE7Label (t : StatedLieTag) (_n _f _p : ℕ) : Prop :=
  t = .E7

@[expose] def GGExcE8FrameLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E8 ∧ (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1 ∨ p ≠ 5)

@[expose] def GGExcE8QuarticFiveLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E8 ∧ p = 5 ∧ ¬ 5 ∣ 2 ^ f - 1 ∧ ¬ 5 ∣ 2 ^ f + 1

@[expose] def GGExcE6SplitLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E6 ∧ p ∣ 2 ^ f - 1 ∧ p ≠ 3

@[expose] def GGExcE6NonsplitLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E6 ∧ ¬ p ∣ 2 ^ f - 1

@[expose] def GGExcE6ThreeLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ f - 1

@[expose] def GGExcTwE6SplitLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .twistedE6 ∧ p ∣ 2 ^ f + 1 ∧ p ≠ 3

@[expose] def GGExcTwE6NonsplitLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .twistedE6 ∧ ¬ p ∣ 2 ^ f + 1

@[expose] def GGExcTwE6ThreeLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .twistedE6 ∧ p = 3 ∧ 3 ∣ 2 ^ f + 1

theorem ggSixBstarNoOffenderAt_F4_of_frame (h : GGSixBstarExcFrameOn .F4 GGExcF4Label) :
    GGSixBstarNoOffenderAt .F4 :=
  have h' := ggNoOffender_of_excFrameOn h fun _ _ _ _ _ hp hp2 =>
    NoOffExc.ggWeylNoOffender_F4 hp hp2
  ggSixBstarNoOffenderAt_of_on .F4 h' h' fun _ _ _ => Or.inl rfl

theorem ggSixBstarNoOffenderAt_E7_of_frame (h : GGSixBstarExcFrameOn .E7 GGExcE7Label) :
    GGSixBstarNoOffenderAt .E7 :=
  have h' := ggNoOffender_of_excFrameOn h fun _ _ _ _ _ hp hp2 =>
    NoOffExc.ggWeylNoOffender_E7 hp hp2
  ggSixBstarNoOffenderAt_of_on .E7 h' h' fun _ _ _ => Or.inl rfl

theorem ggSixBstarNoOffenderAt_E8_of_frame (h : GGSixBstarExcFrameOn .E8 GGExcE8FrameLabel)
    (h5 : GGSixBstarNoOffenderOn GGExcE8QuarticFiveLabel) : GGSixBstarNoOffenderAt .E8 :=
  ggSixBstarNoOffenderAt_of_on .E8
    (ggNoOffender_of_excFrameOn h fun _ _ _ _ _ hp hp2 => NoOffExc.ggWeylNoOffender_E8 hp hp2) h5
    fun _ f p => by
      by_cases h1 : p ∣ 2 ^ f - 1
      · exact Or.inl ⟨rfl, Or.inl h1⟩
      by_cases h2 : p ∣ 2 ^ f + 1
      · exact Or.inl ⟨rfl, Or.inr (Or.inl h2)⟩
      by_cases h3 : p = 5
      · subst h3
        exact Or.inr ⟨rfl, rfl, h1, h2⟩
      · exact Or.inl ⟨rfl, Or.inr (Or.inr h3)⟩

theorem ggSixBstarNoOffenderAt_E6_of_frames (hS : GGSixBstarExcFrameOn .E6 GGExcE6SplitLabel)
    (hN : GGSixBstarExcFrameOn .F4 GGExcE6NonsplitLabel)
    (h3 : GGSixBstarNoOffenderOn GGExcE6ThreeLabel) : GGSixBstarNoOffenderAt .E6 :=
  ggSixBstarNoOffenderAt_of_on₃ .E6
    (ggNoOffender_of_excFrameOn hS fun _ _ _ _ hP hp hp2 =>
      NoOffExc.ggWeylNoOffender_E6 hp hp2 hP.2.2)
    (ggNoOffender_of_excFrameOn hN fun _ _ _ _ _ hp hp2 => NoOffExc.ggWeylNoOffender_F4 hp hp2)
    h3 fun _ f p => by
      by_cases h1 : p ∣ 2 ^ f - 1
      · by_cases hp3 : p = 3
        · subst hp3
          exact Or.inr (Or.inr ⟨rfl, rfl, h1⟩)
        · exact Or.inl ⟨rfl, h1, hp3⟩
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)

theorem ggSixBstarNoOffenderAt_twistedE6_of_frames
    (hS : GGSixBstarExcFrameOn .E6 GGExcTwE6SplitLabel)
    (hN : GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitLabel)
    (h3 : GGSixBstarNoOffenderOn GGExcTwE6ThreeLabel) : GGSixBstarNoOffenderAt .twistedE6 :=
  ggSixBstarNoOffenderAt_of_on₃ .twistedE6
    (ggNoOffender_of_excFrameOn hS fun _ _ _ _ hP hp hp2 =>
      NoOffExc.ggWeylNoOffender_E6 hp hp2 hP.2.2)
    (ggNoOffender_of_excFrameOn hN fun _ _ _ _ _ hp hp2 => NoOffExc.ggWeylNoOffender_F4 hp hp2)
    h3 fun _ f p => by
      by_cases h1 : p ∣ 2 ^ f + 1
      · by_cases hp3 : p = 3
        · subst hp3
          exact Or.inr (Or.inr ⟨rfl, rfl, h1⟩)
        · exact Or.inl ⟨rfl, h1, hp3⟩
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)

@[expose] def GGSixBstarExcFrames : Prop :=
  GGSixBstarExcFrameOn .F4 GGExcF4Label ∧ GGSixBstarExcFrameOn .E7 GGExcE7Label ∧
    GGSixBstarExcFrameOn .E8 GGExcE8FrameLabel ∧ GGSixBstarExcFrameOn .E6 GGExcE6SplitLabel ∧
      GGSixBstarExcFrameOn .F4 GGExcE6NonsplitLabel ∧
        GGSixBstarExcFrameOn .E6 GGExcTwE6SplitLabel ∧
          GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitLabel

@[expose] def GGSixBstarNoOffenderExcRest : Prop :=
  GGSixBstarNoOffenderOn GGExcE6ThreeLabel ∧ GGSixBstarNoOffenderOn GGExcTwE6ThreeLabel ∧
    GGSixBstarNoOffenderOn GGExcE8QuarticFiveLabel

theorem ggSixBstarNoOffenderAt_exc_of_frames (hF : GGSixBstarExcFrames)
    (hR : GGSixBstarNoOffenderExcRest) :
    GGSixBstarNoOffenderAt .F4 ∧ GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧
      GGSixBstarNoOffenderAt .E8 ∧ GGSixBstarNoOffenderAt .twistedE6 := by
  obtain ⟨hF4, hE7, hE8, hE6S, hE6N, hTwS, hTwN⟩ := hF
  obtain ⟨hE6R, hTwR, hE8R⟩ := hR
  exact ⟨ggSixBstarNoOffenderAt_F4_of_frame hF4,
    ggSixBstarNoOffenderAt_E6_of_frames hE6S hE6N hE6R, ggSixBstarNoOffenderAt_E7_of_frame hE7,
    ggSixBstarNoOffenderAt_E8_of_frame hE8 hE8R,
    ggSixBstarNoOffenderAt_twistedE6_of_frames hTwS hTwN hTwR⟩

end Frames

end CFSG.StandardType
