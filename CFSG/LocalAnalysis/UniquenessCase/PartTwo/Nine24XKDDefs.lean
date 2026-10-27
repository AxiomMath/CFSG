module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def NoL2Section (L : Type) [Group L] : Prop :=
  ∀ (X : Subgroup L) (n : ℕ), 1 < n → ¬ IsL2 (Bar2 X) (2 * n)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
