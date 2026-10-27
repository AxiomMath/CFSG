module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

instance instFiniteSemidirectProductPartOne {N H : Type} [Group N] [Group H] [Finite N]
    [Finite H] (φ : H →* MulAut N) : Finite (N ⋊[φ] H) :=
  Finite.of_equiv (N × H) SemidirectProduct.equivProd.symm

@[expose] def IsActionInvariant (B : Type) {S : Type} [Group B] [Group S] [MulDistribMulAction B S]
    (X : Subgroup S) : Prop :=
  ∀ (b : B) (s : S), s ∈ X → b • s ∈ X

@[expose] def ActionCentralizes (B : Type) {S : Type} [Group B] [Group S]
    [MulDistribMulAction B S] (X : Subgroup S) : Prop :=
  ∀ (b : B) (s : S), s ∈ X → b • s = s

@[expose] def MinimalPlaneFactor (B : Type) {S : Type} [Group B] [Group S]
    [MulDistribMulAction B S] (X : Subgroup S) : Prop :=
  IsActionInvariant B X ∧ actionCommutator B X = X ∧
    (∀ U : Subgroup S, U < X → IsActionInvariant B U → ActionCentralizes B U) ∧
    (∃ (b : B) (s : S), s ∈ X ∧ (b • s)⁻¹ * s ∉ inSubgroup frattini X) ∧
    (∀ Y : Subgroup S, inSubgroup frattini X ≤ Y → Y ≤ X → IsActionInvariant B Y →
      Y = inSubgroup frattini X ∨ Y = X) ∧
    (IsElementaryAbelian 2 X ∨
      (⁅X, X⁆ = inSubgroup frattini X ∧ inSubgroup frattini X = inSubgroup Subgroup.center X ∧
        inSubgroup frattini X ≠ ⊥ ∧ IsElementaryAbelian 2 (inSubgroup frattini X) ∧
        ActionCentralizes B (inSubgroup frattini X)))

end CFSG.RankThree.PartOne
