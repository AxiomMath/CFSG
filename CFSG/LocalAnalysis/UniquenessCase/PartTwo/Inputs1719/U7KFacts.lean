module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)

@[expose] def K_U7CentTorus : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (f p r : ℕ),
    CFSG.Open.StatedLieAdmissible .PSU 7 2 f →
      LieModel (K ⧸ Subgroup.center K) .PSU 7 2 f → CFSG.Open.IsQuasisimple K →
        Odd (Nat.card (Subgroup.center K)) →
          p.Prime → p ≠ 2 → p ∣ 2 ^ f + 1 → r.Prime → 7 ≤ r → r ∣ 2 ^ f - 1 →
            ∃ E : Subgroup K, IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
              2 ≤ pRank p (⊤ : Subgroup (Subgroup.centralizer (E : Set K)))

@[expose] def K_U7CartanSylowAbelian : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (f r : ℕ),
    CFSG.Open.StatedLieAdmissible .PSU 7 2 f →
      LieModel (K ⧸ Subgroup.center K) .PSU 7 2 f → CFSG.Open.IsQuasisimple K →
        Odd (Nat.card (Subgroup.center K)) → r.Prime → 7 ≤ r → r ∣ 2 ^ f - 1 →
          ∀ P : Sylow r K, IsMulCommutative (P : Subgroup K)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
