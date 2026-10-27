module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

namespace QA25

@[expose] def M23L34Diagram : Prop :=
  ∀ (M : Type) [Group M] [Finite M], IsSporadic .M23 M → ∀ A S : Subgroup M,
    IsPSL 3 2 2 ↥A → CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
      S ≤ Subgroup.normalizer (A : Set M) → ¬ E2.IsDiagramNontrivial S A (S ⊓ A)

end QA25

end CFSG.Quasithin
