module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRest
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmallLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineTwF4
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly NbrInnerNine


section Nine


theorem largeEvenLabelAll_card_lt_nineSmall {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der ∨ lab.tag = .B2der ∨
      lab.tag = .twB2 ∨ (lab.tag = .A ∧ lab.rank = 2) ∨
      (lab.tag = .triD4 ∧ (p = 3 ∨ p ∣ (2 ^ lab.n) ^ 2 - 1)) ∨
      (lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n - 1)) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  have hn1 : lab.tag = .G2der ∨ lab.tag = .twF4der ∨ lab.tag = .B2der → lab.n = 1 := by
    obtain ⟨t, l, n⟩ := lab
    rintro (ht | ht | ht) <;> dsimp only at ht ⊢ <;> subst ht <;> exact hlab.2.2
  rcases h with ht | ht | ht | ht | ht | ⟨ht, hl⟩ | ⟨ht, hpq⟩ | ⟨ht, hpq⟩
  · exact largeEvenLabelAll_card_lt_G2_all hp hp2 ht
  · by_cases hp3 : p = 3
    · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_G2der hp hlab ht
        (Or.inr (Or.inr (Or.inr ⟨hn1 (Or.inl ht), hp3⟩)))
    · exact largeEvenLabelAll_card_lt_G2der_ne_three hp hp2 hp3 ht
  · by_cases hp3 : p = 3
    · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds hp hlab ht
        (Or.inr (Or.inr (Or.inr ⟨hn1 (Or.inr (Or.inl ht)), hp3⟩)))
    · exact largeEvenLabelAll_card_lt_twF4der_ne_three hp hp2 hp3 hlab ht
  · by_cases hp3 : p = 3
    · exact largeEvenLabelAll_card_lt_b2derThree ⟨hp3, ht⟩
    · exact largeEvenLabelAll_card_lt_b2der_ne_three hp hp2 hp3 ht
  · exact largeEvenLabelAll_card_lt_twB2_all hp hp2 hlab ht
  · exact largeEvenLabelAll_card_lt_A2_all hp hp2 ht hl
  · exact largeEvenLabelAll_card_lt_triD4_of hp hlab ht hpq
  · exact largeEvenLabelAll_card_lt_twF4_sub hp hp2 hlab ht hpq

theorem ggTableBNbrInnerInputOn_nineSmall :
    GGTableBNbrInnerInputOn GGTableBNbrInnerNineSmallLabel := by
  refine ggTableBNbrInnerInputOn_of_labelAll_card_lt fun p lab hp hp2 hlab h => ?_
  rcases h with h | h | h | h | h | h | h | h | ⟨ht, hl⟩
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inl h)).mono
      fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inr (Or.inl h))).mono
      fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inr (Or.inr (Or.inl h)))).mono
      fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inl h))))).mono fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).mono fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).mono fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).mono
        fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))).mono
        fun _ _ _ _ hX _ _ => hX
  · exact largeEvenLabelAll_card_lt_unitaryThree_all hp hp2 hlab ht hl

end Nine


theorem ggTableBNbrInnerInputOn_nineClassical :
    GGTableBNbrInnerInputOn GGTableBNbrInnerNineClassicalLabel :=
  ggTableBNbrInnerInputOn_of_labelAll_card_lt fun _ _ hp hp2 hΛ h =>
    largeEvenLabelAll_card_lt_nineClassical hp hp2 hΛ h

@[expose] def GGTableBNbrInnerRound10Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound9Label p lab ∧ ¬ GGTableBNbrInnerNineSmallLabel p lab ∧
    ¬ GGTableBNbrInnerNineClassicalLabel p lab

section Round10


theorem ggTableBNbrInnerInputOn_round9_of_round10
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound9Label :=
  ((ggTableBNbrInnerInputOn_nineSmall.or ggTableBNbrInnerInputOn_nineClassical).or h).mono
    fun p lab h9 => by
      by_cases hs : GGTableBNbrInnerNineSmallLabel p lab
      · exact Or.inl (Or.inl hs)
      · by_cases hc : GGTableBNbrInnerNineClassicalLabel p lab
        · exact Or.inl (Or.inr hc)
        · exact Or.inr ⟨h9, hs, hc⟩

theorem ggTableBNbrInnerInputOn_round6_of_round10
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound6Label :=
  ggTableBNbrInnerInputOn_round6_of_round9 (ggTableBNbrInnerInputOn_round9_of_round10 h)

theorem ggTableBNbrInnerInput_of_round10
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label) : GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_round9 (ggTableBNbrInnerInputOn_round9_of_round10 h)

end Round10

theorem ggTableBNbrInnerInputOn_round10_of_round9
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound9Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label :=
  h.mono fun _ _ h10 => h10.1

end CFSG.StandardType

end
