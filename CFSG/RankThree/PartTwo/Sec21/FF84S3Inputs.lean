module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

@[expose] def LemmaF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J Z X N : Subgroup G) [(Z.subgroupOf J).Normal] (y : G),
    Z ≤ J → IsPGroup 2 Z → IsSimpleGroup (↥J ⧸ Z.subgroupOf J) →
    Nat.card (↥J ⧸ Z.subgroupOf J) = 168 → y ∈ J → orderOf y = 3 → IsPGroup 2 X → N ≤ X →
    (N.subgroupOf X).Normal → J ≤ Nor X → J ≤ Nor N →
    (∀ x ∈ X, (∃ n ∈ N, y * x * y⁻¹ = x * n) → x ∈ N) → X ≤ N

@[expose] def LemmaH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T N : Subgroup G) (x : G),
    Nat.card K = 60 → IsSimpleGroup K → ¬ 3 ∣ Nat.card T → K ≤ Nor T → N ≤ T → K ≤ Nor N →
    (N.subgroupOf T).Normal → x ∈ K → orderOf x = 3 →
    (∀ u ∈ T, (∃ n ∈ N, x * u * x⁻¹ = u * n) → u ∈ N) →
    (∀ u ∈ T, ∀ v ∈ T, u * v * u⁻¹ * v⁻¹ ∈ N) ∧ (∀ u ∈ T, u ^ 2 ∈ N) ∧
      ∃ r : ℕ, Nat.card T = Nat.card N * 16 ^ r

@[expose] def LemmaQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H P A B' K : Subgroup G),
    KCore.KGroupNonab InCatalog ↥H → IsSylowOf 3 P H → Nat.card P = 9 → A ≤ P → B' ≤ P →
    Nat.card A = 3 → Nat.card B' = 3 → A ⊓ B' = ⊥ → K ≤ H ⊓ CenS B' →
    (K.subgroupOf (H ⊓ CenS B')).Normal → Nat.card K = 60 → IsSimpleGroup K → A ≤ K →
    (¬ ∃ g ∈ H, conjBy g A = B') →
    K ⊔ Opp 3 H ≤ H ∧ ((K ⊔ Opp 3 H).subgroupOf H).Normal

end CFSG.RankThree.PartTwo.Sec21.FF84
