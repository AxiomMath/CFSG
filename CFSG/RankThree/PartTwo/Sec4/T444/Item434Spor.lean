module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Sec

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

@[expose] def IsSporAt (s : TauCeti.SporadicName) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Spor s)

theorem isSpor42_iff {X : Type} [Group X] :
    IsSpor42 X ↔ ∃ s ∈ sporadics42, IsSporAt s X :=
  Iff.rfl

section Families


@[expose] def Item434SporAt (s : TauCeti.SporadicName) : Prop :=
  Item434SecFor (IsSporAt s)

@[expose] def Item434SporAtCard (s : TauCeti.SporadicName) (n : ℕ) : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
        IsSporAt s (layer G ⧸ Subgroup.center (layer G)) →
          Nat.card (A.map (layerConj G)) = n → Concl434 A Q

@[expose] def Item434SporAtNineCover (s : TauCeti.SporadicName) : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
        IsSporAt s (layer G ⧸ Subgroup.center (layer G)) →
          Nat.card (A.map (layerConj G)) = 9 → Subgroup.center (layer G) ≠ ⊥ → Concl434 A Q

theorem item434SporAt_of_card {s : TauCeti.SporadicName} (h9 : Item434SporAtCard s 9)
    (h27 : Item434SporAtCard s 27) : Item434SporAt s := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  rcases hc.card_layerStar with h | ⟨h, -⟩
  · exact h9 G₀ hG₀ H G f hf hker A M Q hc hL h
  · exact h27 G₀ hG₀ H G f hf hker A M Q hc hL h

theorem item434Spor_of_split (h : ∀ s ∈ sporadics42, Item434SporAt s) : Item434Spor := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨s, hs, hX⟩ := isSpor42_iff.mp hL
  exact h s hs G₀ hG₀ H G f hf hker A M Q hc hX

end Families

end CFSG.RankThree.PartTwo.Sec4
