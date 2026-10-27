module

public import CFSG.RankThree.PartOne.S12.InputsEleven

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Blueprint (EvenLieType)

@[expose] def KF128Rank1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J E : Subgroup G) (a d : G),
    p.Prime → 5 ≤ p → CFSG.IsQuasisimple J → EvenLieType (J ⧸ Subgroup.center J) →
    evenRank ↥J ≤ 3 → CFSG.pRank p ↥J ≤ 1 → ¬ p ∣ Nat.card (Subgroup.center J) →
    IsElementaryAbelian p E → E ≤ Subgroup.normalizer (J : Set G) → a ∈ E → d ∈ E → d ∈ J → d ≠ 1 →
    InducesFieldAut p a J →
    (∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      a ∈ Subgroup.normalizer (S : Set G) ∧ d ∈ Subgroup.normalizer (S : Set G)) →
    ∃ y ∈ J, (∃ k : ℕ, orderOf y = p ^ k) ∧ y * d * y⁻¹ = d ∧ y * a * y⁻¹ ≠ a ∧
      ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers d

end CFSG.RankThree.PartOne
