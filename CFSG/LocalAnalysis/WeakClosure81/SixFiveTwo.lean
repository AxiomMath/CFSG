module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveQuot
public import CFSG.RankThree.GF2n.DecompSetupSz
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen
import CFSG.Quasithin.Background.I62Main
import CFSG.RepresentationTheory.SzMartineau.MartineauInput
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Open.SplitBNPair
import CFSG.Permutation.BurnsideSchur
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n (DecompSetup QuotPair)
open Subgroup Matrix
open scoped commutatorElement Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def IsNaturalSum {Q : Type} [Group Q] {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (act : Q → Matrix ι ι F) (K : Subgroup Q) : Prop :=
  ∃ s : Finset (Subgroup Q), s.SupIndep id ∧ s.sup id = K ∧
    ∀ W ∈ s, W.Normal ∧ W ≠ ⊥ ∧ (∀ U : Subgroup Q, U ≤ W → U.Normal → U = ⊥ ∨ U = W) ∧
      ∃ θ : (ι → F) → Q, (∀ v v', θ (v + v') = θ v * θ v') ∧ Function.Injective θ ∧
        Set.range θ = W ∧ ∀ (x : Q) (v : ι → F), θ (act x *ᵥ v) = x * θ v * x⁻¹

end CFSG.LocalAnalysis.WeakClosure81
