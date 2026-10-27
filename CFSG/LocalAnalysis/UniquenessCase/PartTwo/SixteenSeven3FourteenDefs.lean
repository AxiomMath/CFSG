module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.CGT.PushingUp.Defs
public import CFSG.GH74.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Lin2 (ActsRegularlyOn nonIdentity)
open CFSG.RankThree.PartOne (IsNaturalSLTwoModule)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Min1614 (D : Data G) (V U : Subgroup G) : Prop :=
  U ≤ V ∧ ¬ centralizer (U : Set G) ≤ D.M ∧ (E3.mQuot V U : ℕ∞) = rMV D.M V ∧
    rMV D.M V ≤ ((D.k + 2 : ℕ) : ℕ∞)

@[expose] noncomputable def Cartan1614 (D : Data G) (V U : Subgroup G) : Prop :=
  ∃ (n : ℕ) (K X : Subgroup G), rMV D.M V = (n : ℕ∞) ∧
    CFSG.CGT.PushingUp.IsBlockOfInX (centralizer (U : Set G)) K ∧ ¬ K ≤ D.M ∧
    IsNaturalSLTwoModule ↥K n ∧ (K ⊓ D.M).relIndex K = 2 ^ n + 1 ∧ X ≤ K ⊓ D.M ∧
    IsCyclic ↥X ∧ Nat.card X = 2 ^ n - 1 ∧ V ⊓ centralizer (X : Set G) = U ∧
    ActsRegularlyOn X (nonIdentity ⁅V, X⁆)

@[expose] noncomputable def CartanBar1614 (D : Data G) (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (n : ℕ) (x : MulAut (Vtil ⊥ V hV)) : Prop :=
  x ∈ Mbar D.M ⊥ V hV ∧ orderOf x = 2 ^ n - 1 ∧
    Nat.card ↥(commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers x)) = 2 ^ n ∧
    ∀ w ∈ commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers x),
      ∀ w' ∈ commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers x), w ≠ 1 → w' ≠ 1 →
        ∃ g ∈ Subgroup.zpowers x, g w = w'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
