module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank

@[expose] def FactSL3SmallModule : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y R : Subgroup G) [(R.subgroupOf Y).Normal] (F : Type)
    [Field F] [Finite F] (m : ℕ), 2 ≤ m → Nat.card F = 2 ^ m → R ≤ Y → IsPGroup 2 R →
    Nat.card R ≤ 2 ^ (3 * m + 1) →
    (Nonempty (↥Y ⧸ R.subgroupOf Y ≃* ↥(StatedSL 3 F)) ∨
      Nonempty (↥Y ⧸ R.subgroupOf Y ≃* StatedProj (StatedSL 3 F))) →
    (∀ y ∈ Y, (∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ (frattini ↥R).map R.subtype) → y ∈ R) →
    (∀ r ∈ R, r ^ 2 = 1) ∧
      ∃ (e : ↥Y ⧸ R.subgroupOf Y ≃* Matrix.SpecialLinearGroup (Fin 3) F)
        (ψ : ↥R →* Multiplicative (Fin 3 → F)),
        Function.Surjective ψ ∧ (∀ r ∈ ψ.ker, ∀ y ∈ Y, y * (r : G) * y⁻¹ = r) ∧
        ∀ (y : ↥Y) (r r' : ↥R), (r' : G) = y * r * y⁻¹ →
          Multiplicative.toAdd (ψ r') =
            ((e (QuotientGroup.mk y) : Matrix.SpecialLinearGroup (Fin 3) F) :
              Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (ψ r))

end CFSG.Quasithin.H13
