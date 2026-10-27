module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

@[expose] def C626gen : Prop :=
  ∀ p ∈ Dat.sig, ∀ P : Subgroup G,
    IsSylowOf p P (m.M ⊓ normalizer (m.Z : Set G)) → P ≠ ⊥ →
      m.L ≤ gammaL m.L p P ⊔ gammaL m.L m.r m.E

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
