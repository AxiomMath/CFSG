module

public import CFSG.Assembly.InCatalog
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs

@[expose] public section

namespace CFSG.StandardType.FF81

open CFSG.Assembly CFSG.Open

def CatalogueQ1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], (∃ x y : K, x * y ≠ y * x) →
    InCatalog K → 4 ≤ pRank 3 (⊤ : Subgroup K) → ∀ β : MulAut K, β ^ 3 = 1 →
      ∀ O J : Subgroup K, (∀ x : K, x ∈ O ⊔ J ↔ β x = x) → O ⊓ J = ⊥ →
        (∀ x ∈ O, ∀ y ∈ J, x * y = y * x) → Nat.Coprime (Nat.card O) 3 →
        (StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) → False

end CFSG.StandardType.FF81

end
