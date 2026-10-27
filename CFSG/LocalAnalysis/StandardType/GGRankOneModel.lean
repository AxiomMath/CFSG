module

public import CFSG.LieType.Steinberg.PartB
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.Steinberg

@[expose] def GGRankOneModel {K : Type*} [Group K] (D : UniversalRootDatum K) (k : Type*)
    [Field k] : Prop :=
  ∃ (x : (Fin D.rank → ℤ) → k → K)
    (C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ)
    (O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)),
    ChevalleyExtras D k x C O ∧
      ∀ h ∈ ggTorus D, ∀ i : Fin D.rank, ∃ χ : k, ∀ c : k,
        h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c)

end CFSG.StandardType
