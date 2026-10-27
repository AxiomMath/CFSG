module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFourDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBExcSmallRest

@[expose] def GGTableBExcSmallRestLabel (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

@[expose] def GGTableBExcSmallDoneLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2der ∨ (lab.tag = .triD4 ∧ p ≠ 3)

section Labels


theorem largeEvenLabelAll_card_lt_smallRest (h3 : GGTriD4ThreeRankInput)
    (hF : GGTwF4RankInput) (hT : GGTitsThreeRankInput) {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (h : GGTableBExcSmallRestLabel p lab)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  rcases h with ht | ht | ht | ht
  · exact largeEvenLabelAll_card_lt_triD4 (fun _ => h3) hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_twF4 hF hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_G2der hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_twF4der hT hp hlab ht hs

theorem largeEvenLabelAll_card_lt_smallDone {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBExcSmallDoneLabel p lab)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  rcases h with ht | ⟨ht, hp3⟩
  · exact largeEvenLabelAll_card_lt_G2der hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_triD4 (fun h => absurd h hp3) hp hlab ht hs

end Labels

end TableBExcSmallRest

section Inputs


theorem ggBstarInputOn_smallRest (h3 : TableBExcSmallRest.GGTriD4ThreeRankInput)
    (hF : TableBExcSmallRest.GGTwF4RankInput) (hT : TableBExcSmallRest.GGTitsThreeRankInput) :
    GGBstarInputOn TableBExcSmallRest.GGTableBExcSmallRestLabel :=
  ggBstarInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    TableBExcSmallRest.largeEvenLabelAll_card_lt_smallRest h3 hF hT hp hlab h hs

theorem ggStdSubPreInputOn_smallRest (h3 : TableBExcSmallRest.GGTriD4ThreeRankInput)
    (hF : TableBExcSmallRest.GGTwF4RankInput) (hT : TableBExcSmallRest.GGTitsThreeRankInput) :
    GGStdSubPreInputOn TableBExcSmallRest.GGTableBExcSmallRestLabel :=
  ggStdSubPreInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    TableBExcSmallRest.largeEvenLabelAll_card_lt_smallRest h3 hF hT hp hlab h hs

theorem ggBstarInputOn_smallDone :
    GGBstarInputOn TableBExcSmallRest.GGTableBExcSmallDoneLabel :=
  ggBstarInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    TableBExcSmallRest.largeEvenLabelAll_card_lt_smallDone hp hlab h hs

theorem ggStdSubPreInputOn_smallDone :
    GGStdSubPreInputOn TableBExcSmallRest.GGTableBExcSmallDoneLabel :=
  ggStdSubPreInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    TableBExcSmallRest.largeEvenLabelAll_card_lt_smallDone hp hlab h hs

end Inputs

@[expose] def GGTableBOtherRestNoSmall (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBOtherRest4NoF4 p lab ∧ ¬ TableBExcSmallRest.GGTableBExcSmallRestLabel p lab

theorem ggTableBOtherRestNoSmall_cases {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBOtherRestNoSmall p lab)
    (hs : LargeEvenSplit p lab) :
    lab.tag = .E6 ∨ lab.tag = .twE6 ∨ ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p = 3) := by
  obtain ⟨⟨hR, hF4⟩, hS⟩ := h
  rcases ggTableBOtherRest4_cases hp hlab hR hs with h | h | h | h | h | h | ⟨h | h | h, hp3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd (Or.inl h) hS
  · exact absurd (Or.inr (Or.inl h)) hS
  · exact absurd (Or.inr (Or.inr (Or.inl h))) hS
  · exact absurd (Or.inr (Or.inr (Or.inr h))) hS
  · exact absurd ⟨h, hs⟩ hF4
  · exact Or.inr (Or.inr ⟨Or.inl h, hp3⟩)
  · exact Or.inr (Or.inr ⟨Or.inr h, hp3⟩)

section RoundFour


theorem ggBstarInputOn_rest4NoF4_of_noSmall (h3 : TableBExcSmallRest.GGTriD4ThreeRankInput)
    (hF : TableBExcSmallRest.GGTwF4RankInput) (hT : TableBExcSmallRest.GGTitsThreeRankInput)
    (h : GGBstarInputOn GGTableBOtherRestNoSmall) : GGBstarInputOn GGTableBOtherRest4NoF4 :=
  ((ggBstarInputOn_smallRest h3 hF hT).or h).mono fun p lab _ _ hl => by
    by_cases hS : TableBExcSmallRest.GGTableBExcSmallRestLabel p lab
    exacts [Or.inl hS, Or.inr ⟨hl, hS⟩]

theorem ggStdSubPreInputOn_rest4NoF4_of_noSmall (h3 : TableBExcSmallRest.GGTriD4ThreeRankInput)
    (hF : TableBExcSmallRest.GGTwF4RankInput) (hT : TableBExcSmallRest.GGTitsThreeRankInput)
    (h : GGStdSubPreInputOn GGTableBOtherRestNoSmall) :
    GGStdSubPreInputOn GGTableBOtherRest4NoF4 :=
  ((ggStdSubPreInputOn_smallRest h3 hF hT).or h).mono fun p lab _ _ hl => by
    by_cases hS : TableBExcSmallRest.GGTableBExcSmallRestLabel p lab
    exacts [Or.inl hS, Or.inr ⟨hl, hS⟩]

end RoundFour

end CFSG.StandardType
