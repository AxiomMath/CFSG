module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

@[expose] def OuterSL34Input : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U] (K : Subgroup (GLV U)),
    IsNaturalMatrixModule K (StatedSL 3 (GaloisField 2 2)) →
    ∀ (α : ↥K ≃* ↥K) (P : Sylow 2 ↥K), (∀ s ∈ P, α s ∈ P) → (∀ s, α (α s) = s) →
      (¬ ∃ c : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = c * (k : GLV U) * c⁻¹) →
      ∃ s ∈ P, ∃ t ∈ P,
        ¬ ((s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
          (s⁻¹ * α s) * (s⁻¹ * α s) = 1)

end G11

end CFSG.Quasithin
