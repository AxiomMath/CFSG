module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def KFactShape92A5Normalizer : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Shape92 S →
    ∀ (K D : Subgroup S) (T : Sylow 2 S), IsAlt (Bar2 K) 5 → D ≤ K → Nat.card D = 3 →
      normalizer (D : Set S) ≤ normalizer (K : Set S) →
      (T : Subgroup S) ≤ normalizer (K : Set S) → K = ⊤ ∨ LieModel S .PSL 3 5 1

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
