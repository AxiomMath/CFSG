module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.Quasithin

@[expose] def L2BorelFacts : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (Y : Type) [Group Y] [Finite Y] (X U : Subgroup Y), IsPSL 2 2 m ↥X →
    CFSG.QuasithinUnique.IsSylowTwoOf U X →
      Nat.card ↥X = 2 ^ m * (4 ^ m - 1) ∧ Nat.card ↥U = 2 ^ m ∧
      Nat.card ↥(X ⊓ Subgroup.normalizer (U : Set Y)) = 2 ^ m * (2 ^ m - 1) ∧
      IsCoatom ((X ⊓ Subgroup.normalizer (U : Set Y)).subgroupOf X) ∧
      (∀ a ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
        a * b * a⁻¹ * b⁻¹ ∈ U) ∧
      (∃ g ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
        ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ U) ∧
      ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer (U : Set Y),
        ∃ j : ℕ, ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y), r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U

end CFSG.Quasithin.H13.P31X
