module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin

structure E1TypeOne {G : Type*} [Group G] (X S A K : Subgroup G) : Prop where
  le : K ≤ X
  A_le : A ≤ K
  centralizer_le : S ⊓ centralizer (A : Set G) ≤ K
  sylow : IsSylowIn 2 (S ⊓ K) K
  core : ∃ (P : Subgroup G) (p : ℕ), (p = 3 ∨ p = 5) ∧ pCoreOf 2 K ≤ P ∧ P ≤ K ∧
    (P.subgroupOf K).Normal ∧ Nat.card P = Nat.card (pCoreOf 2 K) * p ∧
    (∃ b : ℕ, Nat.card K = Nat.card P * 2 ^ b) ∧ P = pCoreOf 2 K ⊔ ⁅P, A⁆
  index_two : Nat.card A = 2 * Nat.card (A ⊓ pCoreOf 2 K : Subgroup G)
  comm_le : ⁅S ⊓ K, A⁆ ≤ pCoreOf 2 K

end CFSG.Quasithin.H13.NQCore
