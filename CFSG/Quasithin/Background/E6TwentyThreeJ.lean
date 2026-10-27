module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E623CentA3Comp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X S E : Subgroup Y) (a b x : Y),
    CFSG.IsQuasisimple ↥X → IsPGroup 2 (Subgroup.center ↥X) →
    (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 2 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSp 2 2 2) →
    IsSylowTwoOf S X → (∀ s ∈ S, a * s = s * a) →
    a ∈ Subgroup.normalizer (X : Set Y) → a ^ 2 = 1 → a ∉ Subgroup.centralizer (X : Set Y) →
    b ∈ X → (∀ g ∈ X, a * g * a⁻¹ = b * g * b⁻¹) →
    x ∈ Subgroup.normalizer (X : Set Y) → x ^ 3 = 1 → x * a = a * x →
    Nat.card E ≤ 4 →
    (∀ r ∈ pCoreOf 2 (X ⊓ Subgroup.centralizer ({a} : Set Y)), x * r * x⁻¹ * r⁻¹ ∈ E) →
    x ∈ Subgroup.centralizer (X : Set Y)

end E6

end CFSG.Quasithin
