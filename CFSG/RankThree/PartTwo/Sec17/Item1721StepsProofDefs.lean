module

public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Claim17O2Y0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P → CFSG.Open.pCoreOf 2 Y₀ ≤ S

@[expose] def Claim1721SylL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) → ¬ 27 ∣ Nat.card L

@[expose] def KS1721Invert : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (IsLThreePi X ∨ Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) →
      ∀ E : Subgroup X, Nat.card E = 9 → (∀ x ∈ E, x ^ 3 = 1) → ¬ 27 ∣ Nat.card X →
        ∃ g ∈ Subgroup.normalizer (E : Set X), ∀ x ∈ E, g * x * g⁻¹ = x⁻¹

end CFSG.RankThree.PartTwo.Sec17
