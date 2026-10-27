module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSp)

@[expose] def IsSmallTwoSp62 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 3 (GaloisField 2 1))

@[expose] def IsSmallTwoSp48 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 2 (GaloisField 2 3))

@[expose] def IsSmallTwoG28 (X : Type) [Group X] : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ IsoGTwo X q

@[expose] def IsSmallTwoD42 (X : Type) [Group X] : Prop :=
  ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    q.exponent = 1 ∧ Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

theorem isSmallTwoCaseIII_iff {X : Type} [Group X] :
    IsSmallTwoCaseIII X ↔
      IsSmallTwoSp62 X ∨ IsSmallTwoSp48 X ∨ IsSmallTwoG28 X ∨ IsSmallTwoD42 X :=
  Iff.rfl

section Families


@[expose] def Item434SecForCard (P : ∀ (X : Type) [Group X], Prop) (n : ℕ) : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
        P (layer G ⧸ Subgroup.center (layer G)) → Nat.card (A.map (layerConj G)) = n →
          Concl434 A Q

@[expose] def Item434SecForInner (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
        P (layer G ⧸ Subgroup.center (layer G)) → Nat.card (A.map (layerConj G)) = 9 →
          (∀ a ∈ A, ¬ InducesOuter a (layer G)) → Concl434 A Q

theorem item434SecFor_of_card {P : ∀ (X : Type) [Group X], Prop}
    (h9 : Item434SecForCard P 9) (h27 : Item434SecForCard P 27) : Item434SecFor P := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  rcases hc.card_layerStar with h | ⟨h, -⟩
  · exact h9 G₀ hG₀ H G f hf hker A M Q hc hL h
  · exact h27 G₀ hG₀ H G f hf hker A M Q hc hL h

@[expose] def Item434SmallTwoIII_Sp62 : Prop :=
  Item434SecFor IsSmallTwoSp62

@[expose] def Item434SmallTwoIII_Sp48 : Prop :=
  Item434SecFor IsSmallTwoSp48

@[expose] def Item434SmallTwoIII_Sp48_9 : Prop :=
  Item434SecForCard IsSmallTwoSp48 9

@[expose] def Item434SmallTwoIII_Sp48_9Inner : Prop :=
  Item434SecForInner IsSmallTwoSp48

@[expose] def Item434SmallTwoIII_Sp48_27 : Prop :=
  Item434SecForCard IsSmallTwoSp48 27

@[expose] def Item434SmallTwoIII_G28 : Prop :=
  Item434SecFor IsSmallTwoG28

@[expose] def Item434SmallTwoIII_G28_9Inner : Prop :=
  Item434SecForInner IsSmallTwoG28

@[expose] def Item434SmallTwoIII_G28_27 : Prop :=
  Item434SecForCard IsSmallTwoG28 27

@[expose] def Item434SmallTwoIII_D42 : Prop :=
  Item434SecFor IsSmallTwoD42

@[expose] def Item434SmallTwoIII_D42_9 : Prop :=
  Item434SecForCard IsSmallTwoD42 9

@[expose] def Item434SmallTwoIII_D42_27 : Prop :=
  Item434SecForCard IsSmallTwoD42 27

theorem item434SmallTwoIII_of_parts (h62 : Item434SmallTwoIII_Sp62)
    (h48 : Item434SmallTwoIII_Sp48) (hG : Item434SmallTwoIII_G28) (hD : Item434SmallTwoIII_D42) :
    Item434SmallTwoIII := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  rcases isSmallTwoCaseIII_iff.mp hL with h | h | h | h
  · exact h62 G₀ hG₀ H G f hf hker A M Q hc h
  · exact h48 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hG G₀ hG₀ H G f hf hker A M Q hc h
  · exact hD G₀ hG₀ H G f hf hker A M Q hc h

end Families

end CFSG.RankThree.PartTwo.Sec4
