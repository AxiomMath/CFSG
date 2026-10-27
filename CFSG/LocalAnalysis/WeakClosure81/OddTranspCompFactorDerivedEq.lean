module

public import CFSG.LocalAnalysis.WeakClosure81.W183CF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

@[expose] def OddTranspositionCompFactorDerivedEq : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ →
    (∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥) →
    derivedSeries X 1 = derivedSeries X 2 →
    ∀ (T : Type) [Group T], CFSG.Quasithin.E1.IsCompositionFactor X T →
      (∃ a b : T, a * b ≠ b * a) → OddTranspFactor T

end CFSG.LocalAnalysis.WeakClosure81
