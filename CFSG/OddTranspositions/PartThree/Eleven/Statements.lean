module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.Open.StatedDefs
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

@[expose] def Theorem11_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha) →
    (∃ π, IsFiveReflectionModel 3 true π (imageClass hC)) →
    IsFiveReflectionModel 4 true true D

@[expose] def Theorem11_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha) →
    (∃ π, IsFiveReflectionModel 3 false π (imageClass hC)) →
    IsFiveReflectionModel 4 true false D

@[expose] def WongPSp4Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L₁ L₂ : Subgroup G),
    orderOf t = 2 →
    Nonempty (L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) →
    Nonempty (L₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) →
    (∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) → L₁ ⊓ L₂ = Subgroup.zpowers t →
    (L₁ ⊔ L₂).relIndex (Subgroup.centralizer {t}) = 2 →
    Subgroup.centralizer {t} ⊔ CFSG.oddCore G ≠ ⊤ →
    ((∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) ∧
        ∀ x ∈ Subgroup.centralizer {t},
          L₁.map (MulAut.conj x).toMonoidHom = L₁ ∧ L₂.map (MulAut.conj x).toMonoidHom = L₂) ∨
      CFSG.Open.StatedClassicalModel G .PSp 2 5 1

end CFSG.OddTranspositions.PartThree
