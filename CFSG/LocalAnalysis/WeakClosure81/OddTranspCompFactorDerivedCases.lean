module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.WeakClosure81.W183CF
public import CFSG.Sporadic.Co2Cert.Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

@[expose] def OddTranspCompFactorThreeTransp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ →
    (∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥) →
    derivedSeries X 1 = derivedSeries X 2 →
    (∀ d ∈ {x : X | IsConj s x}, ∀ e ∈ {x : X | IsConj s x},
      orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    ∀ (T : Type) [Group T], CFSG.Quasithin.E1.IsCompositionFactor X T →
      (∃ a b : T, a * b ≠ b * a) → OddTranspFactor T

@[expose] def OddTranspCompFactorOFive : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5),
    (∀ x y, b x y = b y x) → (∀ x, (∀ y, b x y = 0) → x = 0) →
    ∀ (T : Type) [Group T],
      CFSG.Quasithin.E1.IsCompositionFactor
        ↥(Subgroup.closure
          (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) T →
      (∃ x y : T, x * y ≠ y * x) → OddTranspFactor T

end CFSG.LocalAnalysis.WeakClosure81
