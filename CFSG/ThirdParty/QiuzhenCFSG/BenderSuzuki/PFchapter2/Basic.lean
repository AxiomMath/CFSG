module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII

universe u v

/-!
# Basic interfaces for Peterfalvi, Part II, Chapter II
-/

/-- Hypothesis (B1), with the prime-order subgroup named explicitly. -/
public structure HypothesisB1
    (G : Type*) [Group G] [Finite G] (V P : Subgroup G) (p : ℕ) : Prop where
  p_prime : Nat.Prime p
  P_le_V : P ≤ V
  P_card : Nat.card P = p
  centralizer_has_involution :
    ∃ x : G, x ∈ Subgroup.centralizer (P : Set G) ∧ IsInvolution x
  centralizer_has_two_rank_one : ¬ TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G))

/-- Hypothesis (B2): no normal subgroup of index `p`. -/
@[expose] public def HypothesisB2
    (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ N : Subgroup G, N.Normal → Nat.card (G ⧸ N) = p → False


/-- The multiplicative group of the near-field in Chapter II, realized as
`C_Q(P)`. -/
@[expose] public def nearFieldStar
    {G : Type*} [Group G] (Q P : Subgroup G) : Subgroup G :=
  Q ⊓ Subgroup.centralizer (P : Set G)


end PFchapter2
end CFSG.BenderSuzuki
namespace And

public theorem section3 {a b c : Prop} (h : a ∧ b ∧ c) : a := by
  exact h.1

public theorem B1 {a b c : Prop} (h : a ∧ b ∧ c) : b := by
  exact h.2.1

public theorem B2 {a b c : Prop} (h : a ∧ b ∧ c) : c := by
  exact h.2.2

end And
