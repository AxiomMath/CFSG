module

public import CFSG.OddTranspositions.PartFour.Fourteen.TheoremFour
public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.Statements
public import CFSG.OddTranspositions.PartThree.FiveReflection
import CFSG.OddTranspositions.PartThree.FiveReflectionFischer

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def Theorem4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → HypothesisE hC →
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
    (¬ ∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
      IsOrthReflection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) →
    (∃ s ∈ imageClass hC, ∃ m f : ℕ, 2 ≤ m ∧ 2 ≤ f ∧
        IsSymplecticTransvection
          (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s ∧
        ∃ t ∈ D, IsOrthReflection G (m + 2) f t) ∨
      (∃ (k : ℕ) (ε π : Bool), 3 ≤ k ∧
        PartThree.IsFiveReflectionModel k (ε == π) π (imageClass hC) ∧
        PartThree.IsFiveReflectionModel (k + 1) ε π D) ∨
      (∃ f n : ℕ, 2 ≤ f ∧ 5 ≤ n ∧
        Nonempty (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
          L2Wreath f n) ∧
        Nonempty (G ≃* L2Wreath f (n + 2)))

theorem theorem4List_of_theorem4 (h4 : Theorem4) (h4O : Theorem4OFour) : Theorem4List := by
  intro G _ _ D hC hrad hE hMZ
  by_cases hO4 : ∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
      IsOrthReflection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s
  · exact h4O G D hC hrad hMZ hO4
  rcases h4 G D hC hrad hE hMZ hO4 with ⟨-, -, m, f, hm, hf, -, t, ht, hO⟩ |
      ⟨k, ε, π, hk, -, hG⟩ | ⟨f, n, hf, -, -, he⟩
  · exact Or.inr (Or.inl ⟨t, ht, m + 2, f, by omega, hf, Or.inr (Or.inr hO)⟩)
  · obtain ⟨b, hb1, hb2, hb3⟩ := PartThree.fischerModel_of_isFiveReflectionModel hG
    exact Or.inr (Or.inr (Or.inl ⟨k + 2, by omega, b, hb1, hb2, hb3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, n + 2, hf, he⟩)))

end CFSG.OddTranspositions.PartFour

end
