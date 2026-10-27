module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def KS1614Trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi ↥(lBarA c L A) →
      ∃ w ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, w ^ 3 ^ k = 1) ∧
        ∃ d ∈ A, d ≠ 1 ∧ (∀ a ∈ A, w * a * w⁻¹ * a⁻¹ ∈ Subgroup.zpowers d) ∧
          ∃ a ∈ A, w * a * w⁻¹ ≠ a

@[expose] noncomputable def Step1614DL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c e : G) (L K : Subgroup G),
    Ctx169 G A c L → Ctx169 G A e K → Subgroup.zpowers e ≠ Subgroup.zpowers c →
    Sec8.IsZ3PGLThreePi ↥(lBarA e K A) →
    ∀ w ∈ K ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, w ^ 3 ^ k = 1) →
    ∀ d ∈ A, d ≠ 1 → (∀ a ∈ A, w * a * w⁻¹ * a⁻¹ ∈ Subgroup.zpowers d) →
      (∃ a ∈ A, w * a * w⁻¹ ≠ a) → w * c * w⁻¹ = c → d ∈ L

end CFSG.RankThree.PartTwo.Sec16
