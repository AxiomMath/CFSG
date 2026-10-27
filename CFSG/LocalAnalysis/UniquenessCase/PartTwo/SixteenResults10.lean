module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_10_2 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    ∀ X S : Subgroup G, X ≤ D.M → CFSG.QuasithinUnique.CharTwo X → IsSylowIn 2 S X →
      CompFactorAutInF D.k X S →
        (X : Set G) = ((X ⊓ centralizer (E3.cClos V D.k S : Set G) : Subgroup G) : Set G) *
          ((X ⊓ normalizer (E3.wClos V 0 S : Set G) : Subgroup G) : Set G)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
