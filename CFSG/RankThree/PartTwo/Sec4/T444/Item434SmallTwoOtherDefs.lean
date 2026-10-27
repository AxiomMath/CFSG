module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def IsSmallTwoOtherL28 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 2 (GaloisField 2 3))

@[expose] def IsSmallTwoOtherL264 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 2 (GaloisField 2 6))

@[expose] def IsSmallTwoOtherU34 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 3 2 2)

@[expose] def IsSmallTwoOtherSp42 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 2 (GaloisField 2 1))

@[expose] def IsSmallTwoOtherSp44 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 2 (GaloisField 2 2))

@[expose] def IsSmallTwoOtherU42 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 4 2 1)

@[expose] def IsSmallTwoOtherU44 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 4 2 2)

@[expose] def IsSmallTwoOtherG22 (X : Type) [Group X] : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoGTwo X q

@[expose] def IsSmallTwoOtherG24 (X : Type) [Group X] : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ IsoGTwo X q

@[expose] def IsSmallTwoOtherTits (X : Type) [Group X] : Prop :=
  ∃ ht : TauCeti.LieTypeIndex.tits.Valid,
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group)

@[expose] def IsSmallTwoOtherL52 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 5 (GaloisField 2 1))

@[expose] def IsSmallTwoOtherL62 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 6 (GaloisField 2 1))

@[expose] def IsSmallTwoOtherL72 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 7 (GaloisField 2 1))

@[expose] def IsSmallTwoOtherL44 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 4 (GaloisField 2 2))

@[expose] def IsSmallTwoOtherSp64 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 3 (GaloisField 2 2))

@[expose] def IsSmallTwoOtherU54 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSU 5 2 2)

@[expose] def IsSmallTwoOtherL3Pi (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 3 (GaloisField 2 6)) ∨ Nonempty (X ≃* projSU 3 2 3)

@[expose] def IsSmallTwoOtherField (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 3 (GaloisField 2 3)) ∨ Nonempty (X ≃* projSU 3 2 6) ∨
    Nonempty (X ≃* projSp 2 (GaloisField 2 6)) ∨ Nonempty (X ≃* projSU 4 2 6) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 6 ∧ IsoGTwo X q) ∨
    (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
      (q.exponent = 2 ∨ q.exponent = 3 ∨ q.exponent = 6) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
    (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid), m ≤ 1 ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group))

@[expose] def Seitz434Other : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsSmallTwoOtherField (X ⧸ Subgroup.center X) →
    ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E →
      (Nat.card E = 9 ∨ (Nat.card E = 27 ∧ Subgroup.center X = ⊥)) →
      CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤

theorem Ctx434Core.false_of_seitz434Other {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (hS : Seitz434Other) (h : Ctx434Core G A M Q)
    (hL : IsSmallTwoOtherField (layer G ⧸ Subgroup.center (layer G))) : False :=
  h.not_le (h.layer_le_of_seitzHyperGamma_eq_top
    (hS (layer G) h.isQuasisimple h.isPGroup_center_layer hL h.layerStar
      h.isElemAbelian_layerStar h.card_layerStar))

section Families


@[expose] def Item434SmallTwoOtherAtL28 : Prop :=
  Item434SecFor IsSmallTwoOtherL28

@[expose] def Item434SmallTwoOtherAtL264 : Prop :=
  Item434SecFor IsSmallTwoOtherL264

@[expose] def Item434SmallTwoOtherAtU34 : Prop :=
  Item434SecFor IsSmallTwoOtherU34

@[expose] def Item434SmallTwoOtherAtSp42 : Prop :=
  Item434SecFor IsSmallTwoOtherSp42

@[expose] def Item434SmallTwoOtherAtSp44 : Prop :=
  Item434SecFor IsSmallTwoOtherSp44

@[expose] def Item434SmallTwoOtherAtU42 : Prop :=
  Item434SecFor IsSmallTwoOtherU42

@[expose] def Item434SmallTwoOtherAtU44 : Prop :=
  Item434SecFor IsSmallTwoOtherU44

@[expose] def Item434SmallTwoOtherAtG22 : Prop :=
  Item434SecFor IsSmallTwoOtherG22

@[expose] def Item434SmallTwoOtherAtG24 : Prop :=
  Item434SecFor IsSmallTwoOtherG24

@[expose] def Item434SmallTwoOtherAtTits : Prop :=
  Item434SecFor IsSmallTwoOtherTits

@[expose] def Item434SmallTwoOtherAtL52 : Prop :=
  Item434SecFor IsSmallTwoOtherL52

@[expose] def Item434SmallTwoOtherAtL62 : Prop :=
  Item434SecFor IsSmallTwoOtherL62

@[expose] def Item434SmallTwoOtherAtL72 : Prop :=
  Item434SecFor IsSmallTwoOtherL72

@[expose] def Item434SmallTwoOtherAtL44 : Prop :=
  Item434SecFor IsSmallTwoOtherL44

@[expose] def Item434SmallTwoOtherAtSp64 : Prop :=
  Item434SecFor IsSmallTwoOtherSp64

@[expose] def Item434SmallTwoOtherAtU54 : Prop :=
  Item434SecFor IsSmallTwoOtherU54

@[expose] def Item434OtherL3Pi : Prop :=
  Item434SecFor IsSmallTwoOtherL3Pi

@[expose] def Item434SmallTwoOtherAtField : Prop :=
  Item434SecFor IsSmallTwoOtherField

theorem item434SmallTwoOtherAtField_of (hS : Seitz434Other) : Item434SmallTwoOtherAtField :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hL => (hc.false_of_seitz434Other hS hL).elim

theorem item434SmallTwoOther_of_parts (hL28 : Item434SmallTwoOtherAtL28)
    (hL264 : Item434SmallTwoOtherAtL264) (hU34 : Item434SmallTwoOtherAtU34)
    (hSp42 : Item434SmallTwoOtherAtSp42) (hSp44 : Item434SmallTwoOtherAtSp44)
    (hU42 : Item434SmallTwoOtherAtU42) (hU44 : Item434SmallTwoOtherAtU44)
    (hG22 : Item434SmallTwoOtherAtG22) (hG24 : Item434SmallTwoOtherAtG24)
    (hTits : Item434SmallTwoOtherAtTits) (hL52 : Item434SecFor IsSmallTwoOtherL52)
    (hL62 : Item434SecFor IsSmallTwoOtherL62) (hL72 : Item434SecFor IsSmallTwoOtherL72)
    (hL44 : Item434SmallTwoOtherAtL44) (hSp64 : Item434SmallTwoOtherAtSp64)
    (hU54 : Item434SmallTwoOtherAtU54) (hL3Pi : Item434OtherL3Pi)
    (hField : Item434SmallTwoOtherAtField) : Item434SmallTwoOther := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  rcases hL with ⟨n, hn, hL2⟩ | ⟨n, hn, hL3⟩ | ⟨n, hn, hU3⟩ | ⟨n, hn, hSp4⟩ | ⟨n, hn, hU4⟩ |
    ⟨q, hq2, hq3, hq, hG2⟩ | ⟨q, hv, hq2, hq1, hq, hD4⟩ | ⟨m, hm, hm1, hF4⟩ | ⟨ht, hT⟩ |
    (h52 | h62 | h72 | h44 | h64 | h54)
  ·
    rcases hn with rfl | rfl
    · exact hL28 G₀ hG₀ H G f hf hker A M Q hc hL2
    · exact hL264 G₀ hG₀ H G f hf hker A M Q hc hL2
  ·
    rcases hn with rfl | rfl
    · exact hField G₀ hG₀ H G f hf hker A M Q hc (Or.inl hL3)
    · exact hL3Pi G₀ hG₀ H G f hf hker A M Q hc (Or.inl hL3)
  ·
    rcases hn with rfl | rfl | rfl
    · exact hU34 G₀ hG₀ H G f hf hker A M Q hc hU3
    · exact hL3Pi G₀ hG₀ H G f hf hker A M Q hc (Or.inr hU3)
    · exact hField G₀ hG₀ H G f hf hker A M Q hc (Or.inr (Or.inl hU3))
  ·
    rcases hn with rfl | rfl | rfl
    · exact hSp42 G₀ hG₀ H G f hf hker A M Q hc hSp4
    · exact hSp44 G₀ hG₀ H G f hf hker A M Q hc hSp4
    · exact hField G₀ hG₀ H G f hf hker A M Q hc (Or.inr (Or.inr (Or.inl hSp4)))
  ·
    rcases hn with rfl | rfl | rfl
    · exact hU42 G₀ hG₀ H G f hf hker A M Q hc hU4
    · exact hU44 G₀ hG₀ H G f hf hker A M Q hc hU4
    · exact hField G₀ hG₀ H G f hf hker A M Q hc (Or.inr (Or.inr (Or.inr (Or.inl hU4))))
  ·
    have he := q.exponent_pos
    rcases (show q.exponent = 1 ∨ q.exponent = 2 ∨ q.exponent = 6 by omega) with h1 | h2 | h6
    · exact hG22 G₀ hG₀ H G f hf hker A M Q hc ⟨q, hq2, h1, hG2⟩
    · exact hG24 G₀ hG₀ H G f hf hker A M Q hc ⟨q, hq2, h2, hG2⟩
    · exact hField G₀ hG₀ H G f hf hker A M Q hc
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq2, h6, hG2⟩)))))
  ·
    have he := q.exponent_pos
    exact hField G₀ hG₀ H G f hf hker A M Q hc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hv, hq2, by omega, hD4⟩))))))
  ·
    exact hField G₀ hG₀ H G f hf hker A M Q hc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, hm1, hF4⟩))))))
  · exact hTits G₀ hG₀ H G f hf hker A M Q hc ⟨ht, hT⟩
  · exact hL52 G₀ hG₀ H G f hf hker A M Q hc h52
  · exact hL62 G₀ hG₀ H G f hf hker A M Q hc h62
  · exact hL72 G₀ hG₀ H G f hf hker A M Q hc h72
  · exact hL44 G₀ hG₀ H G f hf hker A M Q hc h44
  · exact hSp64 G₀ hG₀ H G f hf hker A M Q hc h64
  · exact hU54 G₀ hG₀ H G f hf hker A M Q hc h54

end Families

end CFSG.RankThree.PartTwo.Sec4
