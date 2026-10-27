module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.lemma_1_21

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Lemma 1.22
**Stmt**:
Let $p$ be a prime.
Let $G$ be a $p$-group.
Let $N$ be a normal subgroup of $G$ with $|N| = p^k$.
For every non-negative integer $r \le k$, $N$ contains a normal subgroup of $G$ having order $p^r$.
-/

public theorem CFSG.lemma_1_22 {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] [Fact (IsPGroup p G)]
    (N : Subgroup G) (hN : N.Normal) (k : ℕ) (hcard : Nat.card N = p ^ k) :
    ∀ r : ℕ, r ≤ k → ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = p ^ r := by
  simpa using
    exists_normal_subgroup_card_pow_of_normal (G := G) (p := p) N hN (k := k) hcard

end
