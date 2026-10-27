module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] noncomputable def gammaL {G : Type} [Group G] [Finite G] (X : Subgroup G) (p : ℕ)
    (P : Subgroup G) : Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ P) (_ : 1 ≤ CFSG.Open.pRank p Q), X ⊓ normalizer (Q : Set G)

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def C626gen : Prop :=
  ∀ p ∈ uniqueFourSigma m.M, ∀ P : Subgroup G,
    IsSylowOf p P (m.M ⊓ normalizer (m.Z : Set G)) → P ≠ ⊥ →
      m.L ≤ gammaL m.L p P ⊔ gammaL m.L m.r m.E

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
