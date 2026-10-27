module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListCorrected

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

@[expose] def OddTranspListDerivedEqThreeTransp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2 →
    (∀ d ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
      ∀ e ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    OddTranspListAlt X s

@[expose] def OddTranspListDerivedEqOFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2 →
    (∃ n : ℕ, 4 ≤ n ∧ ∃ b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5),
      (∀ x y, b x y = b y x) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      CFSG.Open.fischerCentralQuotientModel
        {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
        (Subgroup.closure
          (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) →
    OddTranspListAlt X s

end CFSG.LocalAnalysis.WeakClosure81
