module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

@[expose] def K_FunHypOmega :
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
    CFSG.ClassicalInvolution.Disconnected.AschTight.HypOmegaGen
      {Kb : Subgroup X | IsFundamentalOver q Kb}

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
