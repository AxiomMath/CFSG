module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListCorrected

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

@[expose] def OddTranspListThreeTranspReflSixCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2 →
    (∀ d ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
      ∀ e ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    Subgroup.center X ≠ ⊥ →
    ∀ f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3), (∀ x y, f x y = f y x) →
      (∀ x, (∀ y, f x y = 0) → x = 0) →
      (¬ ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
        ∀ x ∈ T, f x x = 0) →
      fischerCentralQuotientModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1) →
      OddTranspListAlt X s

@[expose] def OddTranspListThreeTranspReflLift : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2 →
    (∀ d ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
      ∀ e ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    Subgroup.center X ≠ ⊥ →
    ∀ (m : ℕ), 7 ≤ m → ∀ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) → (∀ x, (∀ y, f x y = 0) → x = 0) →
      fischerCentralQuotientModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1) →
      OddTranspListAlt X s

@[expose] def OddTranspListThreeTranspFischer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2 →
    (∀ d ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
      ∀ e ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    ((∃ φ : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.Fi22,
        CFSG.Blueprint.Fischer.Pair _
          (φ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}) ∧
        ∀ E : Set CFSG.Blueprint.NativeSporadic.Fi22, CFSG.Blueprint.Fischer.Pair _ E →
          E = φ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}) ∨
      (∃ φ : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.Fi23,
        CFSG.Blueprint.Fischer.Pair _
          (φ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}) ∧
        ∀ E : Set CFSG.Blueprint.NativeSporadic.Fi23, CFSG.Blueprint.Fischer.Pair _ E →
          E = φ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}) ∨
      (∃ φ : X ⧸ Subgroup.center X ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime,
        CFSG.Blueprint.Fischer.Pair _
          (φ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}) ∧
        ∀ E : Set (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime),
          CFSG.Blueprint.Fischer.Pair _ E →
          E = φ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x})) →
    OddTranspListAlt X s

end CFSG.LocalAnalysis.WeakClosure81
