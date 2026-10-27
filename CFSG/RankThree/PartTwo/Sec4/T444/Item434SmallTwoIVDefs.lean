module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSU projSp projOmegaPlus f4TwoIndex)

@[expose] def IsSmallTwoSp82 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 4 (GaloisField 2 1))

@[expose] def IsSmallTwoU52 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 5 2 1)

@[expose] def IsSmallTwoU62 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 6 2 1)

@[expose] def IsSmallTwoO8p (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projOmegaPlus 4 (GaloisField 2 1))

@[expose] def IsSmallTwoF42 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)

@[expose] def IsSmallTwoU48 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 4 2 3)

@[expose] def IsSmallTwoU58 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 5 2 3)

theorem isSmallTwoCaseIV_iff {X : Type} [Group X] :
    IsSmallTwoCaseIV X ↔
      IsSmallTwoSp82 X ∨ IsSmallTwoU52 X ∨ IsSmallTwoU62 X ∨ IsSmallTwoO8p X ∨
        IsSmallTwoF42 X ∨ IsSmallTwoU48 X ∨ IsSmallTwoU58 X :=
  Iff.rfl

section Families


@[expose] def Item434SecForCardInner (P : ∀ (X : Type) [Group X], Prop) (n : ℕ) : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
        P (layer G ⧸ Subgroup.center (layer G)) → Nat.card (A.map (layerConj G)) = n →
          (∀ a ∈ A, ¬ InducesOuter a (layer G)) → Concl434 A Q

@[expose] def Item434SecForCardOuter (P : ∀ (X : Type) [Group X], Prop) (n : ℕ) : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
        P (layer G ⧸ Subgroup.center (layer G)) → Nat.card (A.map (layerConj G)) = n →
          (∃ a ∈ A, InducesOuter a (layer G)) → Concl434 A Q

theorem item434SecForCard_of_inner_outer {P : ∀ (X : Type) [Group X], Prop} {n : ℕ}
    (hI : Item434SecForCardInner P n) (hO : Item434SecForCardOuter P n) :
    Item434SecForCard P n := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL hn
  by_cases hout : ∃ a ∈ A, InducesOuter a (layer G)
  · exact hO G₀ hG₀ H G f hf hker A M Q hc hL hn hout
  · push Not at hout
    exact hI G₀ hG₀ H G f hf hker A M Q hc hL hn hout

@[expose] def Item434SmallTwoIV_Sp82 : Prop :=
  Item434SecFor IsSmallTwoSp82

@[expose] def Item434SmallTwoIV_U52 : Prop :=
  Item434SecFor IsSmallTwoU52

@[expose] def Item434SmallTwoIV_U62_27 : Prop :=
  Item434SecForCard IsSmallTwoU62 27

@[expose] def Item434SmallTwoIV_O8p_27Outer : Prop :=
  Item434SecForCardOuter IsSmallTwoO8p 27

@[expose] def Item434SmallTwoIV_O8p_27 : Prop :=
  Item434SecForCard IsSmallTwoO8p 27

@[expose] def Item434SmallTwoIV_O8p : Prop :=
  Item434SecFor IsSmallTwoO8p

@[expose] def Item434SmallTwoIV_F42_27 : Prop :=
  Item434SecForCard IsSmallTwoF42 27

@[expose] def Item434SmallTwoIV_U48_27 : Prop :=
  Item434SecForCard IsSmallTwoU48 27

@[expose] def Item434SmallTwoIV_U58 : Prop :=
  Item434SecFor IsSmallTwoU58

theorem item434SmallTwoIV_of_parts (hSp : Item434SmallTwoIV_Sp82) (hU52 : Item434SmallTwoIV_U52)
    (hU62 : Item434SecFor IsSmallTwoU62) (hO8 : Item434SmallTwoIV_O8p) (hF4 : Item434SecFor IsSmallTwoF42)
    (hU48 : Item434SecFor IsSmallTwoU48) (hU58 : Item434SmallTwoIV_U58) : Item434SmallTwoIV := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  rcases isSmallTwoCaseIV_iff.mp hL with h | h | h | h | h | h | h
  · exact hSp G₀ hG₀ H G f hf hker A M Q hc h
  · exact hU52 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hU62 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hO8 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hF4 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hU48 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hU58 G₀ hG₀ H G f hf hker A M Q hc h

end Families

end CFSG.RankThree.PartTwo.Sec4
