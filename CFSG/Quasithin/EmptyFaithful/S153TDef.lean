module

public import CFSG.Quasithin.Background.C1GNBlocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Input1463FourAbel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I T T₀ : Subgroup G),
    IsSQTKTC I → CharTwo I → IsSylowTwoOf T₀ I → IsPGroup 2 T → T₀ ≤ T → T₀.relIndex T = 2 →
    T ⊓ I = T₀ →
    (∀ C : Subgroup G, C ≤ T₀ → C ≠ ⊥ → T ≤ Subgroup.normalizer (C : Set G) →
      I ⊓ Subgroup.normalizer (C : Set G) ≤ T₀) →
    (pCoreOf 2 I).relIndex T₀ = 2 →
    ∀ x ∈ pCoreOf 2 I, ∀ y ∈ pCoreOf 2 I, x * y = y * x

end CFSG.Quasithin
