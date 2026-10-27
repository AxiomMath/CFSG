module

public import CFSG.OddTranspositions.PartThree.Twelve.FourShapes
public import CFSG.OddTranspositions.PartThree.Twelve.Minimal
import CFSG.OddTranspositions.PartThree.Twelve.SixUnitary

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def TwelveSpBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    Theorem4Below (Nat.card G) →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → HypothesisE hC →
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
    (¬ ∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
      IsOrthReflection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) →
    hC.alpha = {hC.d} →
    ∀ s ∈ imageClass hC, ∀ m f : ℕ, 4 ≤ m → 2 ≤ f →
      IsSymplecticTransvection
        (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s →
      TheoremFourConclusion hC

@[expose] def TwelveEightU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    Theorem4Below (Nat.card G) →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → HypothesisE hC →
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
    (¬ ∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
      IsOrthReflection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) →
    hC.alpha = {hC.d} →
    ∀ s ∈ imageClass hC, ∀ f : ℕ, 2 ≤ f →
      ¬ IsUnitaryTransvection
        (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s

@[expose] def TwelveF5Branch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    Theorem4Below (Nat.card G) →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → HypothesisE hC →
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
    (¬ ∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
      IsOrthReflection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) →
    hC.alpha = {hC.d} →
    ∀ (k : ℕ) (ε π : Bool), 4 ≤ k → PartThree.IsFiveReflectionModel k ε π (imageClass hC) →
      TheoremFourConclusion hC

section Certs


theorem theorem4_of_branches (h91 : Theorem9_1) (h101 : Theorem10_1) (h111 : Theorem11_1)
    (h112 : Theorem11_2) (hSp : TwelveSpBranch) (hU : TwelveEightU) (hF5 : TwelveF5Branch) :
    Theorem4 := by
  refine theorem4_of_step h91 h101 h111 h112 fun G _ _ D hC hIH hrad hE hMZ hO4 hH => ?_
  obtain ⟨hα, ⟨s, hs, m, f, hm, hf, hSp' | hU'⟩ | ⟨k, ε, π, hk, h5⟩⟩ := twelveFour hC hMZ hH
  · exact hSp G D hC hIH hrad hE hMZ hO4 hα s hs m f hm hf hSp'
  · obtain rfl := eq_four_of_isUnitaryTransvection hIH hC hMZ hα hs hm hf hU'
    exact (hU G D hC hIH hrad hE hMZ hO4 hα s hs f hf hU').elim
  · exact hF5 G D hC hIH hrad hE hMZ hO4 hα k ε π hk h5

end Certs

end CFSG.OddTranspositions.PartThree
