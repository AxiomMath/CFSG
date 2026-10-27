module

public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Item1724PtsThreePrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
        (∃ B, IsHyperplane A B ∧ a ∈ B ∧ lB A B ≠ ⊥) →
        3 ∣ Nat.card (oPrimeResidualOf p (delta A (lB A) (Subgroup.centralizer ({a} : Set G)))) →
        ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({a} : Set G) ∧
          A ≤ Subgroup.normalizer (R : Set G) ∧ ¬ 3 ∣ Nat.card R ∧
          ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf p), S' ≤ R

@[expose] def Item1724NormThreePrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ D ∈ scriptQPi A (lB A) ⊤ (piOf p), D ≠ ⊥ →
        3 ∣ Nat.card (oPrimeResidualOf p (delta A (lB A) (Subgroup.normalizer (D : Set G)))) →
        ∃ R : Subgroup G, R ≤ Subgroup.normalizer (D : Set G) ∧
          A ≤ Subgroup.normalizer (R : Set G) ∧ ¬ 3 ∣ Nat.card R ∧
          ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (D : Set G)) (piOf p), S' ≤ R

end CFSG.RankThree.PartTwo.Sec17
