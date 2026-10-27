module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

@[expose] def FF79KCenterJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (J : Subgroup G), (n = 4 ∨ n = 5) →
    CFSG.IsQuasisimple ↥J → IsTypeLnq n 2 1 J → Nat.card ↥(Subgroup.center ↥J) ∣ 2

@[expose] def FF79KAutCentP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (J P : Subgroup G), (n = 4 ∨ n = 5) →
    CFSG.IsQuasisimple ↥J → IsTypeLnq n 2 1 J → IsSylowOf 3 P J →
    (P ⊔ CenS J).relIndex (Nor J ⊓ CenS P) ≤ 2 ∧ ∀ g ∈ Nor J, ∃ j ∈ J, j⁻¹ * g ∈ CenS P

@[expose] def FF79KCentAlpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (J P : Subgroup G), (n = 4 ∨ n = 5) →
    CFSG.IsQuasisimple ↥J → IsTypeLnq n 2 1 J → IsSylowOf 3 P J →
    ∀ α ∈ P, orderOf α = 3 → ∀ Y : Subgroup G, Y ≤ Nor J → Y ≤ Cen α →
      Nat.Coprime 3 (Nat.card Y) → (∀ j ∈ J ⊓ Cen α, ∀ y ∈ Y, j * y * j⁻¹ ∈ Y) →
      Y ≤ CenS P ∧ (n = 5 → Y ≤ CenS J)

end CFSG.RankThree.PartTwo.Sec21.FF79
