module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Recognition.St84.Hyp

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

structure CaseAGen (X : Setup Γ G) : Prop where
  two_le_n1 : 2 ≤ X.n 1
  n1_le_n0 : X.n 1 ≤ X.n 0
  card_S : Nat.card X.S = 2 ^ (3 * X.n 0 + 3 * X.n 1)
  card_Q0 : Nat.card (X.Q 0) = 2 ^ (2 * X.n 0 + 3 * X.n 1)
  card_Q1 : Nat.card (X.Q 1) = 2 ^ (3 * X.n 0 + 2 * X.n 1)
  Z0_eq : X.Z 0 = centerOf (X.L 0)
  card_Z0 : Nat.card (X.Z 0) = 2 ^ X.n 1
  natZ1 : NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1)
  center_Q0 : centerOf (X.Q 0) = X.Z 0
  special_Q0 : IsSpecialPGroup 2 ↥(X.Q 0)
  sec_Q0 : IsElemSec (X.Z 0) (X.Q 0)
  indec_Q0 : ⁅X.Q 0, oTwoRes (X.L 0)⁆ = X.Q 0
  perfect_L0 : ⁅X.L 0, X.L 0⁆ = X.L 0
  normal_A1 : X.Gi 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G)
  sec_W1 : IsElemSec (X.Q 0 ⊓ X.Q 2) (X.Q 1)
  irred_W1 : ∀ Y : Subgroup G, X.Q 0 ⊓ X.Q 2 ≤ Y → Y ≤ X.Q 1 →
    X.Gi 1 ≤ Subgroup.normalizer (Y : Set G) → Y = X.Q 0 ⊓ X.Q 2 ∨ Y = X.Q 1
  fpf_W1 : ∀ k ∈ X.L 1, Odd (orderOf k) → k ≠ 1 → ∀ w ∈ X.Q 1,
    ⁅w, k⁆ ∈ X.Q 0 ⊓ X.Q 2 → w ∈ X.Q 0 ⊓ X.Q 2
  A1_eq : X.Q 0 ⊓ X.Q 2 = (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1
  D_inf : (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓ X.Z 1 = ⊥
  card_D : Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) = 2 ^ X.n 0
  elem_A1 : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2)
  comm_A1 : ⁅X.Q 0 ⊓ X.Q 2, X.L 1⁆ ≤ X.Z 1
  comm_D : ⁅X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G), X.Q 1⁆ = X.Z 1
  D_cent : (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓
    Subgroup.centralizer (X.Q 1 : Set G) = ⊥
  gen_Q0 : ∀ N : Subgroup G, X.Z 1 ≤ N → N ≤ X.Q 0 →
    X.L 0 ≤ Subgroup.normalizer (N : Set G) → N = X.Q 0

end Setup

end CFSG.Quasithin.St84

end
