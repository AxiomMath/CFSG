module

public import CFSG.Quasithin.EmptyFaithful.S1565A
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.F918P5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Shape15365 {Y : Type} [Group Y] (n : ℕ) (Ks : Subgroup Y) : Prop :=
  IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks ∨ IsPSU 3 2 n ↥Ks ∨ IsPSL 3 2 n ↥Ks ∨ E2.IsSp4Prime n ↥Ks

@[expose] def Input15365Odd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Ks MKs : Subgroup Y) (n : ℕ), 2 ≤ n → Even n →
    Shape15365 n Ks → E2.IsBorelIn Ks MKs → 3 ∣ Nat.card MKs

section Conclusions

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

@[expose] def ChiefFreeBelow15365 (hF : HypF918 T V L V₁ Vp H K) (M I : Subgroup G) : Prop :=
  haveI := factElem hF (le_conjClosure Vp H)
  S1565.ChiefFreeBelow (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
    ((H ⊓ M).subgroupOf H) (subM V₁ (conjClosure Vp H) (conjClosure I H))

end Conclusions

end CFSG.Quasithin
