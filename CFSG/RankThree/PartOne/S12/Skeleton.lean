module

public import CFSG.RankThree.PartOne.S12.Assembly
public import CFSG.RankThree.PartOne.S12.LThreeAt
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def torusWeylHasPCore {G : Type} [Group G] (p : ℕ) (E : Subgroup G) : Prop :=
  CFSG.pCore p ↥(torusWeyl E) ≠ ⊥

@[expose] def Node126 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → torusIrreducible E ∨ torusWeylHasPCore p E ∨
      Outcome152Five p E A (lieGenerated p E)

@[expose] def Node127 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) →
      torusHasTransvection p E → torusWeylHasPCore p E

@[expose] def Node128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → (∃ X : Subgroup G, X ∈ sectionTenZeroStar p A ∧ X ∈ sectionTenTwo p A) →
      torusHasTransvection p E

@[expose] def Node129 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → ¬ torusWeylHasPCore p E

theorem sec13_one_of_nodes (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E)) :
    torusIrreducible E ∧ ¬ torusHasTransvection p E ∧
      sectionTenZeroStar p A ⊆ sectionTenOne p A := by
  have hO := h129 G p A c L E h hT
  have hnot : ¬ torusHasTransvection p E := fun ht => hO (h127 G p A c L E h hT ht)
  refine ⟨?_, hnot, fun X hX => ?_⟩
  · rcases h126 G p A c L E h with hirr | hP | hfive
    · exact hirr
    · exact absurd hP hO
    · exact absurd hfive hT
  · by_contra hX1
    exact hnot (h128 G p A c L E h ⟨X, hX, (sectionTenZeroStar_subset p A).2.2.1 hX.2, hX1⟩)

@[expose] def Node138 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A →
      Outcome152Five p E A (lieGenerated p E)

@[expose] def Node1320 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → E = A →
      ¬ IsLThreeTypeAt p L →
      Outcome152Two p E A (lieGenerated p E) ∨ Outcome152Three p E A (lieGenerated p E) ∨
        Outcome152Four p E A (lieGenerated p E)

@[expose] def Node141 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → E = A →
      (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
      Outcome152One p E A (lieGenerated p E)

theorem sec12to14_of_nodes (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129)
    (h138 : Node138) (h1320 : Node1320) (h141 : Node141) : Sec12to14Claim := by
  intro G _ _ p A c L E h
  by_cases hT : Outcome152Five p E A (lieGenerated p E)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hT)))
  obtain ⟨-, -, hZ⟩ := sec13_one_of_nodes h126 h127 h128 h129 h hT
  by_cases hEA : E = A
  · by_cases hall : ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J
    · exact Or.inl (h141 G p A c L E h hT hEA hall)
    · obtain ⟨J, hJ, hJn⟩ : ∃ J : Subgroup G, J ∈ sectionTenZeroStar p A ∧ ¬ IsLThreeTypeAt p J := by
        by_contra hcon
        exact hall fun J hJ => by_contra fun hJn => hcon ⟨J, hJ, hJn⟩
      obtain ⟨cJ, hcJA, hcJ1, hJc⟩ := mem_thetaComponentFamily_iff.mp
        ((sectionTenZeroStar_subset p A).2.2.1 hJ.2)
      have hJ' : Sec12Hyp G p A cJ J E :=
        ⟨h.setup, hcJA, hcJ1, ⟨⟨hJ, hZ hJ⟩, hJc⟩, h.E_elem, h.E_le, h.E_max⟩
      rcases h1320 G p A cJ J E hJ' hT hEA hJn with h2 | h3 | h4
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact absurd (h138 G p A c L E h hT hEA) hT

end CFSG.RankThree.PartOne
