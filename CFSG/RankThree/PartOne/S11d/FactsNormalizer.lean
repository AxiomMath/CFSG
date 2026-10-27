module

public import CFSG.RankThree.PartOne.S11d.Facts11

public section

namespace CFSG.RankThree.PartOne

open CFSG

@[expose] def FieldAutNormalizerPower : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (K : Subgroup G) (a x : G) (m : ℤ),
    FieldAutSetting p K a → 7 ≤ p → x ∈ Subgroup.normalizer (K : Set G) →
    x * a * x⁻¹ * a ^ (-m) ∈ K ⊔ Subgroup.centralizer (K : Set G) → (p : ℤ) ∣ m - 1

end CFSG.RankThree.PartOne
