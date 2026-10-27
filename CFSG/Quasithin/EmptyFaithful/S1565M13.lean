module

public import CFSG.Quasithin.Background.F918P5
public import CFSG.Quasithin.EmptyFaithful.S1565H

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Layer

attribute [local instance] commGroupOfFact

@[expose] def FFnatEltConcl {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}
    (hF : HypF918 T V L V₁ Vp H K) (M I : Subgroup G) : Prop :=
  haveI := factElem hF (le_conjClosure Vp H)
  ∃ t₀ : ↥H, (t₀ : G) ∈ M ∧ ∃ m : ℕ, Odd m ∧
    (∀ a ∈ subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆,
      ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) t₀) ^ m) a = a) ∧
    ∀ a ∈ subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆,
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) t₀ a * a⁻¹ ∈
        subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆ ⊓
          S1565.fixModSub (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
            ((conjClosure K T).subgroupOf H) (subM V₁ (conjClosure Vp H) (conjClosure I H)) →
      a ∈ subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆ ⊓
        S1565.fixModSub (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
          ((conjClosure K T).subgroupOf H) (subM V₁ (conjClosure Vp H) (conjClosure I H))

end Layer

end CFSG.Quasithin
