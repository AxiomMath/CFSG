module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def A312PairCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSQTKCat X → CFSG.pCore 2 X = ⊥ →
    ∀ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → ∀ B₁ ∈ lFamily T,
      ∀ B₂ ∈ lFamily T, B₁ ≠ ⊤ → B₂ ≠ ⊤ → B₁ ≠ B₂ →
      T ≤ Subgroup.normalizer (B₁ : Set X) → T ≤ Subgroup.normalizer (B₂ : Set X) →
      ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂ → Nonempty (ModO2 B₁ ≃* ModO2 B₂) → False

end CFSG.Quasithin.Vol2.Ch10
