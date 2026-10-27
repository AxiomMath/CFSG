module

public import CFSG.Blueprint.Chevalley
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley

@[expose] def RankG24Fact : Prop :=
  ∀ (K : Type) [Field K], Nat.card K = 4 →
    ∀ E : Subgroup ↥(adjointGroup .G2 K), CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 6

@[expose] def RankG24FrobCentFact : Prop :=
  ∀ (K : Type) [Field K], Nat.card K = 4 → ∀ δ : K →+* K, (∀ c, δ c = c ^ 2) →
    ∀ E : Subgroup ↥(adjointGroup .G2 K), CFSG.Open.IsElemAbelian 2 E →
      (∀ x ∈ E, Units.map (entrywiseHom δ) (x : ModGL .G2 K) = (x : ModGL .G2 K)) →
        Nat.card E ≤ 2 ^ 3

end CFSG.Quasithin
