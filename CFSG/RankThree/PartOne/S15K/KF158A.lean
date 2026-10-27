module

public import CFSG.RankThree.PartOne.S15K.KtData

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

@[expose] def KF158ASplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
    (Outcome152One p E A (lieGenerated p E) ∨ Outcome152Two p E A (lieGenerated p E) ∨
      Outcome152Three p E A (lieGenerated p E) ∨ Outcome152Four p E A (lieGenerated p E)) →
    ∃ t ∈ reflectionSet p E, SplitKt p E t

@[expose] def KF158AFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∃ t ∈ reflectionSet p E, ∃ K J : Subgroup G, IsKt p E t K ∧ K ≤ J ∧ autMovedInG E t ≤ K ∧
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥A ∧
      J ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (J : Set G)) ∧
      ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
        S = ⁅S, A⁆

theorem kf158A_conclusion_of_split {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hEA : E = A)
    (hs : ∃ t ∈ reflectionSet p E, SplitKt p E t) :
    ∃ t ∈ reflectionSet p E, ∃ K J : Subgroup G, IsKt p E t K ∧ K ≤ J ∧ autMovedInG E t ≤ K ∧
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥A ∧
      J ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (J : Set G)) ∧
      ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
        S = ⁅S, A⁆ := by
  obtain ⟨t, ht, hst⟩ := hs
  obtain ⟨hKt, hmov, hcard, hθ, hS⟩ := splitKt_data h hEA ht hst
  exact ⟨t, ht, kZero p E t, kZero p E t, hKt, le_rfl, hmov, hcard, hθ, hS⟩

theorem kf158A_of_inputs (hS : KF158ASplit) (hF : KF158AFive) : KF158A := by
  intro G _ _ p A c L E h15 hF' hout
  by_cases h5 : Outcome152Five p E A (lieGenerated p E)
  · exact hF G p A c L E h15 hF' h5
  · have h14 : Outcome152One p E A (lieGenerated p E) ∨ Outcome152Two p E A (lieGenerated p E) ∨
        Outcome152Three p E A (lieGenerated p E) ∨ Outcome152Four p E A (lieGenerated p E) := by
      rcases hout with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd h h5
    have hEA : E = A := by
      rcases h14 with h | h | h | h
      · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
        exact hEA
      · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
        exact hEA
      · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
        exact hEA
      · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
        exact hEA
    exact kf158A_conclusion_of_split h15.h12 hEA (hS G p A c L E h15 hF' h14)

end CFSG.RankThree.PartOne.S15K
