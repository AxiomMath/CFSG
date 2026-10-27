module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Sec

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def IsCharThreeL2Three (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 2 (GaloisField 3 1))

@[expose] def IsCharThreeL2Nine (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 2 (GaloisField 3 2))

@[expose] def IsCharThreeL2Large (X : Type) [Group X] : Prop :=
  ∃ e : ℕ, 3 ≤ e ∧ Nonempty (X ≃* projSL 2 (GaloisField 3 e))

@[expose] def IsCharThreeL3Three (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 3 (GaloisField 3 1))

@[expose] def IsCharThreeU3Three (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 3 3 1)

@[expose] def IsCharThreeL3Large (X : Type) [Group X] : Prop :=
  ∃ e : ℕ, 2 ≤ e ∧ e ≤ 3 ∧ Nonempty (X ≃* projSL 3 (GaloisField 3 e))

@[expose] def IsCharThreeU3Large (X : Type) [Group X] : Prop :=
  ∃ e : ℕ, 2 ≤ e ∧ e ≤ 3 ∧ Nonempty (X ≃* projSU 3 3 e)

@[expose] def IsCharThreeG2 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group)

@[expose] def IsCharThreeL4 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 4 (GaloisField 3 1))

@[expose] def IsCharThreeU4 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 4 3 1)

@[expose] def IsCharThreeRee (X : Type) [Group X] : Prop :=
  ∃ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group)

theorem isLie42CharThree_cases {X : Type} [Group X] (h : IsLie42CharThree X) :
    IsCharThreeL2Three X ∨ IsCharThreeL2Nine X ∨ IsCharThreeL2Large X ∨ IsCharThreeL3Three X ∨
      IsCharThreeU3Three X ∨ IsCharThreeL3Large X ∨ IsCharThreeU3Large X ∨ IsCharThreeG2 X ∨
      IsCharThreeL4 X ∨ IsCharThreeU4 X ∨ IsCharThreeRee X := by
  rcases h with ⟨e, he, hL2⟩ | hRee | (⟨e, he1, he3, hL3 | hU3⟩ | hG2 | hL4 | hU4)
  · rcases (show e = 1 ∨ e = 2 ∨ 3 ≤ e by omega) with rfl | rfl | h3
    · exact Or.inl hL2
    · exact Or.inr <| Or.inl hL2
    · exact Or.inr <| Or.inr <| Or.inl ⟨e, h3, hL2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr hRee
  · rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | h2
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hL3
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e, h2, he3, hL3⟩
  · rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | h2
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hU3
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e, h2, he3, hU3⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hG2
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inl hL4
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inl hU4

section Families


@[expose] def Item434CharThreeL2Three : Prop :=
  Item434SecFor IsCharThreeL2Three

@[expose] def Item434CharThreeL2Nine : Prop :=
  Item434SecFor IsCharThreeL2Nine

@[expose] def Item434CharThreeL2Large : Prop :=
  Item434SecFor IsCharThreeL2Large

@[expose] def Item434CharThreeL3Three : Prop :=
  Item434SecFor IsCharThreeL3Three

@[expose] def Item434CharThreeU3Three : Prop :=
  Item434SecFor IsCharThreeU3Three

@[expose] def Item434CharThreeL3Large : Prop :=
  Item434SecFor IsCharThreeL3Large

@[expose] def Item434CharThreeU3Large : Prop :=
  Item434SecFor IsCharThreeU3Large

@[expose] def Item434CharThreeG2 : Prop :=
  Item434SecFor IsCharThreeG2

@[expose] def Item434CharThreeL4 : Prop :=
  Item434SecFor IsCharThreeL4

@[expose] def Item434CharThreeU4 : Prop :=
  Item434SecFor IsCharThreeU4

@[expose] def Item434CharThreeRee : Prop :=
  Item434SecFor IsCharThreeRee

theorem item434CharThree_of_split (h23 : Item434CharThreeL2Three) (h29 : Item434CharThreeL2Nine)
    (h2L : Item434CharThreeL2Large) (h33 : Item434CharThreeL3Three)
    (hU33 : Item434CharThreeU3Three) (h3L : Item434CharThreeL3Large)
    (hU3L : Item434CharThreeU3Large) (hG2 : Item434CharThreeG2) (hL4 : Item434CharThreeL4)
    (hU4 : Item434CharThreeU4) (hRee : Item434CharThreeRee) : Item434CharThree := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  rcases isLie42CharThree_cases hL with h | h | h | h | h | h | h | h | h | h | h
  · exact h23 G₀ hG₀ H G f hf hker A M Q hc h
  · exact h29 G₀ hG₀ H G f hf hker A M Q hc h
  · exact h2L G₀ hG₀ H G f hf hker A M Q hc h
  · exact h33 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hU33 G₀ hG₀ H G f hf hker A M Q hc h
  · exact h3L G₀ hG₀ H G f hf hker A M Q hc h
  · exact hU3L G₀ hG₀ H G f hf hker A M Q hc h
  · exact hG2 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hL4 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hU4 G₀ hG₀ H G f hf hker A M Q hc h
  · exact hRee G₀ hG₀ H G f hf hker A M Q hc h

end Families

end CFSG.RankThree.PartTwo.Sec4
