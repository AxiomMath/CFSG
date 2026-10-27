module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Recognition.St84.Hyp

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

section TypeZero

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

structure TreeSp44Data (X : Setup Γ G) : Prop where
  card_S : Nat.card X.S = 2 ^ 8
  card_edge : Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) = 2 ^ 8 * 3 ^ 2
  elem_left : IsElemAbelian 2 (pCoreOf 2 (X.L 0))
  card_left : Nat.card (pCoreOf 2 (X.L 0)) = 2 ^ 6
  center_left : Nat.card ↥(centerOf (X.L 0)) = 2 ^ 2
  nat_left : NatSec (X.L 0) (centerOf (X.L 0)) (pCoreOf 2 (X.L 0))
  indec_left : ⁅pCoreOf 2 (X.L 0), X.L 0⁆ = pCoreOf 2 (X.L 0)
  elem_right : IsElemAbelian 2 (pCoreOf 2 (X.L 1))
  card_right : Nat.card (pCoreOf 2 (X.L 1)) = 2 ^ 6
  center_right : Nat.card ↥(centerOf (X.L 1)) = 2 ^ 2
  nat_right : NatSec (X.L 1) (centerOf (X.L 1)) (pCoreOf 2 (X.L 1))
  indec_right : ⁅pCoreOf 2 (X.L 1), X.L 1⁆ = pCoreOf 2 (X.L 1)
  card_inf : Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)) = 2 ^ 4

structure TreeG24Data (X : Setup Γ G) : Prop where
  card_S : Nat.card X.S = 2 ^ 12
  card_edge : Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) = 2 ^ 12 * 3 ^ 2
  special_left : IsSpecialPow 2 (2 ^ 2) 2 ↥(pCoreOf 2 (X.L 0))
  center_left : centerOf (pCoreOf 2 (X.L 0)) = centerOf (X.L 0)
  indec_left : ⁅pCoreOf 2 (X.L 0), X.L 0⁆ = pCoreOf 2 (X.L 0)
  card_right : Nat.card (pCoreOf 2 (X.L 1)) = 2 ^ 10
  special_right : IsSpecialPGroup 2 ↥(pCoreOf 2 (X.L 1))
  card_center_right : Nat.card ↥(centerOf (pCoreOf 2 (X.L 1))) = 2 ^ 4
  natZ_right : NatSec (X.L 1) ⊥ (centerOf (pCoreOf 2 (X.L 1)))
  mid_right : ∃ W : Subgroup G, centerOf (pCoreOf 2 (X.L 1)) ≤ W ∧
    W ≤ pCoreOf 2 (X.L 1) ∧ Nat.card W = 2 ^ 6 ∧
    ⁅W, X.L 1⁆ ≤ centerOf (pCoreOf 2 (X.L 1)) ∧
    NatSec (X.L 1) W (pCoreOf 2 (X.L 1))
  card_inf : Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)) = 2 ^ 8

structure TreeG24Extra (X : Setup Γ G) : Prop where
  irr_left : ∀ Y : Subgroup G, centerOf (pCoreOf 2 (X.L 0)) ≤ Y →
    Y ≤ pCoreOf 2 (X.L 0) → X.Gi 0 ≤ Subgroup.normalizer (Y : Set G) →
      Y = centerOf (pCoreOf 2 (X.L 0)) ∨ Y = pCoreOf 2 (X.L 0)
  orth_left : ∃ E : Subgroup G, centerOf (pCoreOf 2 (X.L 0)) ≤ E ∧
    E ≤ pCoreOf 2 (X.L 0) ∧ (centerOf (pCoreOf 2 (X.L 0))).relIndex E = 16 ∧
    X.L 0 ≤ Subgroup.normalizer (E : Set G) ∧
    (∃ l ∈ X.L 0, ∃ e ∈ E, ⁅l, e⁆ ∉ centerOf (pCoreOf 2 (X.L 0))) ∧
    ¬ NatSec (X.L 0) (centerOf (pCoreOf 2 (X.L 0))) E
  comm_right : ⁅pCoreOf 2 (X.L 1), X.L 1⁆ = pCoreOf 2 (X.L 1)

end Setup

end TypeZero

end CFSG.Quasithin.St84
