module

public import CFSG.OddTranspositions.PartThree.EightFive.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Local
public import CFSG.Timmesfeld.Bridge.OddTranspDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

@[expose] def EightFiveCaseTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → ¬ O4PairData G D →
    (∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card G → Theorem8_5At Y) →
    ∀ w v : G, IsTriangle D hC.d w v → v ∈ DalphaStar D hC.alpha →
    ∀ n : ℕ, Odd n → 1 < n → orderOf (hC.d * v * w) = 2 * n →
    ∀ z : G, (hC.d * v * w) ^ n = z →
      (∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * hC.d * k⁻¹ = x) →
      CFSG.BenderSuzuki.IsBenderGroup
        (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)) →
      ¬ CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z) →
      (∀ q ∈ CFSG.pCore 2 (localGroup D z), (q : G) * hC.d * (q : G)⁻¹ ∈ hC.alpha) →
      ∃ d ∈ D, Commute d hC.d ∧ Commute d v ∧ Commute d w

end CFSG.OddTranspositions.PartThree
