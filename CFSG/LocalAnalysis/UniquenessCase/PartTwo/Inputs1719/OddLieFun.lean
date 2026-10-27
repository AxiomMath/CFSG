module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

variable {G : Type} [Group G] [Finite G]

@[expose] def K_FunNonempty :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (r q : ℕ),
    r.Prime → r ≠ 2 →
    (∃ (t : StatedLieTag) (n f : ℕ),
      StatedLieAdmissible t n r f ∧ q = r ^ f ∧
        LieModel (X ⧸ Subgroup.center X) t n r f) →
    CFSG.Open.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) →
    (¬ IsL2Over17 (X ⧸ Subgroup.center X) q) →
    (¬ IsL3EpsOdd17 (X ⧸ Subgroup.center X) r) →
    (¬ IsReeOver17 X q) →
    3 < q →
    ∀ P : Sylow 2 X, (FunSet (fundPred q) X (P : Subgroup X)).Nonempty

@[expose] def K_FunCommute :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (r q : ℕ),
    r.Prime → r ≠ 2 →
    (∃ (t : StatedLieTag) (n f : ℕ),
      StatedLieAdmissible t n r f ∧ q = r ^ f ∧
        LieModel (X ⧸ Subgroup.center X) t n r f) →
    CFSG.Open.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) →
    (¬ IsL2Over17 (X ⧸ Subgroup.center X) q) →
    (¬ IsL3EpsOdd17 (X ⧸ Subgroup.center X) r) →
    (¬ IsReeOver17 X q) →
    3 < q →
    ∀ P : Sylow 2 X, ∀ K₁ ∈ FunSet (fundPred q) X (P : Subgroup X),
      ∀ K₂ ∈ FunSet (fundPred q) X (P : Subgroup X), K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
