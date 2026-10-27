module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3 IsL3 IsSp4 IsSL3)

abbrev ShapePred : Type 1 := ∀ {Y : Type} [Group Y], Subgroup Y → Prop

@[expose] def ShapeL2 : ShapePred := fun L => OddShape5 L ∧ IsL2 ↥L 2

@[expose] def ShapeU3 : ShapePred := fun L => OddShape5 L ∧ IsU3 ↥L 2

@[expose] def ShapeL3 : ShapePred := fun L => OddShape5 L ∧ IsL3 ↥L 2

@[expose] def ShapeSp4 : ShapePred := fun L => OddShape5 L ∧ IsSp4 ↥L 2

@[expose] def ShapeSL3 : ShapePred := fun L => OddShape5 L ∧ IsSL3 ↥L 2

@[expose] def InvolutionCentralizerOn (Sh : ShapePred) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (b : Y), Sh L →
    b ∈ normalizer (L : Set Y) → b * b = 1 →
    (∀ x ∈ L, x * b = b * x → ∀ l ∈ L, (x * x) * l = l * (x * x)) →
    ∃ s ∈ L, s * s = 1 ∧ ∃ c ∈ centralizer (L : Set Y), b = s * c

@[expose] def FourGroupInnerOn (Sh : ShapePred) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A : Subgroup Y), Sh L →
    A ≤ normalizer (L : Set Y) → IsElemAbelian 2 A → Nat.card A = 4 →
    A ⊓ centralizer (L : Set Y) = ⊥ → K1In L A → A ≤ L ⊔ centralizer (L : Set Y)

@[expose] def BorelRankOneOn (Sh : ShapePred) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S : Subgroup Y), Sh L → IsSylowIn 2 S L →
    ∀ P : Subgroup Y, L ⊓ normalizer (S : Set Y) ≤ P → P ≤ L →
      P = L ⊓ normalizer (S : Set Y) ∨ P = L

@[expose] def BorelRankTwoOn (Sh : ShapePred) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S : Subgroup Y), Sh L → IsSylowIn 2 S L →
    ∃ P₁ P₂ : Subgroup Y, IsMaxParabolicMod ⊥ L P₁ ∧ IsMaxParabolicMod ⊥ L P₂ ∧
      L ⊓ normalizer (S : Set Y) ≤ P₁ ∧ L ⊓ normalizer (S : Set Y) ≤ P₂ ∧
      (∀ l ∈ L, conjSubgroup P₁ l ≠ P₂) ∧
      ∀ P : Subgroup Y, L ⊓ normalizer (S : Set Y) ≤ P → P ≤ L →
        P = L ⊓ normalizer (S : Set Y) ∨ P = P₁ ∨ P = P₂ ∨ P = L

@[expose] def ChoiceOfKOn (Sh : ShapePred) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S A : Subgroup Y), Sh L → IsSylowIn 2 S L →
    A ≤ S → IsElemAbelian 2 A → Nat.card A = 4 → K1In L A → TISIn L A →
    ∃ K : Subgroup Y, K ≤ L ∧ A ≤ K ∧ ¬ A ≤ oTwoMod ⊥ K ∧
      HasQuotShape K (oTwoMod ⊥ K : Set Y) (fun X _ => IsL2 X 2) ∧ IsSylowIn 2 (S ⊓ K) K ∧
      (K ⊓ (L ⊓ normalizer (S : Set Y))).relIndex K = 5 ∧
      (RankTwoShape L → ¬ (∀ a ∈ A, ∀ s ∈ S, a * s = s * a) →
        ∃ P : Subgroup Y, IsMaxParabolicMod ⊥ L P ∧ K = oddResMod ⊥ P)

@[expose] def BorelGL32SylowOn (Sh : ShapePred) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S : Subgroup Y), Sh L → IsSylowIn 2 S L →
    ∀ (E : Type) [Group E], ElemAbOrderEight E →
      ∀ (W : Subgroup (MulAut E)) (X : Type) [Group X] (ψ : ↥W →* X), Function.Surjective ψ →
        ∀ φ : ↥(L ⊓ normalizer (S : Set Y)) →* X,
          S.subgroupOf (L ⊓ normalizer (S : Set Y)) ≤ φ.ker

@[expose] def BorelGL32CenterOn (Sh : ShapePred) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S : Subgroup Y), Sh L → IsSylowIn 2 S L →
    ∀ (E : Type) [Group E], ElemAbOrderEight E →
      ∀ (W : Subgroup (MulAut E)) (X : Type) [Group X] (ψ : ↥W →* X), Function.Surjective ψ →
        ∀ φ : ↥(L ⊓ normalizer (S : Set Y)) →* X,
          (S ⊓ centralizer (S : Set Y)).subgroupOf (L ⊓ normalizer (S : Set Y)) ≤ φ.ker

theorem InvolutionCentralizerFact.of_shapes (h₂ : InvolutionCentralizerOn ShapeL2)
    (hU : InvolutionCentralizerOn ShapeU3) (hL : InvolutionCentralizerOn ShapeL3)
    (hS : InvolutionCentralizerOn ShapeSp4) (hC : InvolutionCentralizerOn ShapeSL3) :
    InvolutionCentralizerFact := by
  intro Y _ _ L b hL5 hb hb2 hx
  obtain ⟨hq, hodd, hs⟩ := hL5
  rcases hs with hs | hs | hs | hs | hs
  · exact h₂ Y L b ⟨⟨hq, hodd, Or.inl hs⟩, hs⟩ hb hb2 hx
  · exact hU Y L b ⟨⟨hq, hodd, Or.inr (Or.inl hs)⟩, hs⟩ hb hb2 hx
  · exact hL Y L b ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inl hs))⟩, hs⟩ hb hb2 hx
  · exact hS Y L b ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inr (Or.inl hs)))⟩, hs⟩ hb hb2 hx
  · exact hC Y L b ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inr (Or.inr hs)))⟩, hs⟩ hb hb2 hx

theorem FourGroupInnerFact.of_shapes (h₂ : FourGroupInnerOn ShapeL2)
    (hU : FourGroupInnerOn ShapeU3) (hL : FourGroupInnerOn ShapeL3)
    (hS : FourGroupInnerOn ShapeSp4) (hC : FourGroupInnerOn ShapeSL3) :
    FourGroupInnerFact := by
  intro Y _ _ L A hL5 hA hAe hA4 hAC hK
  obtain ⟨hq, hodd, hs⟩ := hL5
  rcases hs with hs | hs | hs | hs | hs
  · exact h₂ Y L A ⟨⟨hq, hodd, Or.inl hs⟩, hs⟩ hA hAe hA4 hAC hK
  · exact hU Y L A ⟨⟨hq, hodd, Or.inr (Or.inl hs)⟩, hs⟩ hA hAe hA4 hAC hK
  · exact hL Y L A ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inl hs))⟩, hs⟩ hA hAe hA4 hAC hK
  · exact hS Y L A ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inr (Or.inl hs)))⟩, hs⟩ hA hAe hA4 hAC hK
  · exact hC Y L A ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inr (Or.inr hs)))⟩, hs⟩ hA hAe hA4 hAC hK

theorem BorelOvergroupFact.of_shapes (h₂ : BorelRankOneOn ShapeL2) (hU : BorelRankOneOn ShapeU3)
    (hL : BorelRankTwoOn ShapeL3) (hS : BorelRankTwoOn ShapeSp4)
    (hC : BorelRankTwoOn ShapeSL3) : BorelOvergroupFact := by
  intro Y _ _ L S hL5 hSy
  obtain ⟨hq, hodd, hs⟩ := hL5
  refine ⟨fun h1 P hBP hPL => ?_, fun h2 => ?_⟩
  · rcases h1 with h1 | h1
    · exact h₂ Y L S ⟨⟨hq, hodd, hs⟩, h1⟩ hSy P hBP hPL
    · exact hU Y L S ⟨⟨hq, hodd, hs⟩, h1⟩ hSy P hBP hPL
  · rcases h2 with h2 | h2 | h2
    · exact hL Y L S ⟨⟨hq, hodd, hs⟩, h2⟩ hSy
    · exact hS Y L S ⟨⟨hq, hodd, hs⟩, h2⟩ hSy
    · exact hC Y L S ⟨⟨hq, hodd, hs⟩, h2⟩ hSy

theorem ChoiceOfKFact.of_shapes (h₂ : ChoiceOfKOn ShapeL2) (hU : ChoiceOfKOn ShapeU3)
    (hL : ChoiceOfKOn ShapeL3) (hS : ChoiceOfKOn ShapeSp4) (hC : ChoiceOfKOn ShapeSL3) :
    ChoiceOfKFact := by
  intro Y _ _ L S A hL5 hSy hAS hAe hA4 hK hT
  obtain ⟨hq, hodd, hs⟩ := hL5
  rcases hs with hs | hs | hs | hs | hs
  · exact h₂ Y L S A ⟨⟨hq, hodd, Or.inl hs⟩, hs⟩ hSy hAS hAe hA4 hK hT
  · exact hU Y L S A ⟨⟨hq, hodd, Or.inr (Or.inl hs)⟩, hs⟩ hSy hAS hAe hA4 hK hT
  · exact hL Y L S A ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inl hs))⟩, hs⟩ hSy hAS hAe hA4 hK hT
  · exact hS Y L S A ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inr (Or.inl hs)))⟩, hs⟩ hSy hAS hAe hA4 hK hT
  · exact hC Y L S A ⟨⟨hq, hodd, Or.inr (Or.inr (Or.inr (Or.inr hs)))⟩, hs⟩ hSy hAS hAe hA4 hK hT

theorem BorelGL32Fact.of_shapes (hU : BorelGL32SylowOn ShapeU3)
    (hL : BorelGL32CenterOn ShapeL3) (hS : BorelGL32CenterOn ShapeSp4)
    (hC : BorelGL32CenterOn ShapeSL3) : BorelGL32Fact := by
  intro Y _ _ L S hL5 hSy E _ hE W X _ ψ hψ φ
  obtain ⟨hq, hodd, hs⟩ := hL5
  refine ⟨fun h1 => hU Y L S ⟨⟨hq, hodd, hs⟩, h1⟩ hSy E hE W X ψ hψ φ, fun h2 => ?_⟩
  rcases h2 with h2 | h2 | h2
  · exact hL Y L S ⟨⟨hq, hodd, hs⟩, h2⟩ hSy E hE W X ψ hψ φ
  · exact hS Y L S ⟨⟨hq, hodd, hs⟩, h2⟩ hSy E hE W X ψ hψ φ
  · exact hC Y L S ⟨⟨hq, hodd, hs⟩, h2⟩ hSy E hE W X ψ hψ φ

structure CitedShapeFacts : Prop where
  f1_U3 : InvolutionCentralizerOn ShapeU3
  f1_L3 : InvolutionCentralizerOn ShapeL3
  f1_Sp4 : InvolutionCentralizerOn ShapeSp4
  f1_SL3 : InvolutionCentralizerOn ShapeSL3
  f2_U3 : FourGroupInnerOn ShapeU3
  f2_L3 : FourGroupInnerOn ShapeL3
  f2_Sp4 : FourGroupInnerOn ShapeSp4
  f2_SL3 : FourGroupInnerOn ShapeSL3
  f3_L3 : BorelRankTwoOn ShapeL3
  f3_Sp4 : BorelRankTwoOn ShapeSp4
  f3_SL3 : BorelRankTwoOn ShapeSL3

structure GapShapeFacts : Prop where
  f4_U3 : ChoiceOfKOn ShapeU3
  f4_L3 : ChoiceOfKOn ShapeL3
  f4_Sp4 : ChoiceOfKOn ShapeSp4
  f4_SL3 : ChoiceOfKOn ShapeSL3
  f6_U3 : BorelGL32SylowOn ShapeU3
  f6_L3 : BorelGL32CenterOn ShapeL3
  f6_Sp4 : BorelGL32CenterOn ShapeSp4
  f6_SL3 : BorelGL32CenterOn ShapeSL3

end CFSG.LocalAnalysis.WeakClosure81

end
