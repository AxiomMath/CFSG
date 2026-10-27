module

public import CFSG.RankThree.PartOne.S12.Sec15Lemmas

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

@[expose] def thetaLayer (p : ℕ) {G : Type*} [Group G] (e : G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ Y ∈ thetaComponentsAt p e, x ∈ Y}

@[expose] def KFInnLayer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) → E = A →
    ∀ e ∈ E, e ≠ 1 → (∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) →
    ∀ x ∈ E, ∃ l ∈ E ⊓ thetaLayer p e,
      ∃ c' ∈ E ⊓ Subgroup.centralizer (thetaLayer p e : Set G), x = l * c'

@[expose] def Node1510Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    E = A → ∀ U : Subgroup G, U ≤ E → U ≠ ⊥ → Subgroup.normalizer (U : Set G) ≤ lieNormalizer p E

@[expose] def Node1510Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ U : Subgroup G, U ≤ E → U ≠ ⊥ → Subgroup.normalizer (U : Set G) ≤ lieNormalizer p E

theorem node1510_of_cases (hEven : Node1510Even) (hFive : Node1510Five) : Node1510 := by
  intro G _ _ p A c L E h15 hF hout U hUE hU1
  by_cases hEA : E = A
  · exact hEven G p A c L E h15 hF hout hEA U hUE hU1
  · rcases hout with h1 | h2 | h3 | h4 | h5
    · obtain ⟨-, -, -, -, -, hEA', -⟩ := h1
      exact absurd hEA' hEA
    · obtain ⟨-, -, -, -, -, hEA', -⟩ := h2
      exact absurd hEA' hEA
    · obtain ⟨-, -, -, -, -, hEA', -⟩ := h3
      exact absurd hEA' hEA
    · obtain ⟨-, -, -, -, -, hEA', -⟩ := h4
      exact absurd hEA' hEA
    · exact hFive G p A c L E h15 hF h5 U hUE hU1

end CFSG.RankThree.PartOne
