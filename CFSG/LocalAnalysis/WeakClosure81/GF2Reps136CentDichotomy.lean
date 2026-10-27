module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136CentSingleton
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

theorem cent_dichotomy {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} (hk : k ≤ 3) {I : Fin k → Subgroup Q}
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i → J = ⊥ ∨ J = I i)
    (hspan : ⨆ i, I i = ⊤) (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {X : Subgroup (MulAut Q)} (hXc : X ≤ Subgroup.centralizer (Λ : Set (MulAut Q)))
    (hXp : ⁅X, X⁆ = X) :
    X = ⊥ ∨ (k = 3 ∧ (∀ i j, SecIsoOn Λ (I i) ⊥ (I j) ⊥) ∧ Nat.card X = 168 ∧
      (∀ i, Nat.card (I i) ^ 3 = Nat.card Q)) := by
  exact w1369_cent_dichotomy_aux k hQ hstab hsimple hspan hind hend hk hXc hXp

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
