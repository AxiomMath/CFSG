module

public import CFSG.RankThree.PartOne.S12.InputsTable

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def InnerWeylFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K F : Subgroup G) (r : ℕ), F ≤ K → IsElementaryAbelian 7 F →
    1 ≤ r → r ≤ 8 → RowData 7 K F r → ∀ c x : G, x ∈ Subgroup.normalizer (K : Set G) →
      x ∈ Subgroup.normalizer (F : Set G) → x ^ 3 = 1 → c ∈ F → c ≠ 1 → x * c = c * x →
      (∃ f ∈ F, x * f * x⁻¹ ≠ f) →
      ∃ y ∈ K, y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
        (∃ k : ℕ, y ^ (3 ^ k) = 1) ∧ y * c * y⁻¹ ≠ c

end CFSG.RankThree.PartOne
