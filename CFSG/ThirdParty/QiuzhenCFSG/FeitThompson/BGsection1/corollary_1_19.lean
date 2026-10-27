module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Corollary 1.19
**Stmt**:
Let $G$ be a group.
(a) If $S$ is a cyclic Sylow subgroup of $G$, then either $S \cap G' = 1$ or $S \subset G'$.
(b) If $G$ is a $Z$-group, then $G'$ is a Hall subgroup of $G$.
-/

-- Corollary 1.19(a)
public theorem CFSG.corollary_1_19_a {G : Type*} [Group G] [Finite G] :
    ∀ (p : ℕ) [Fact p.Prime],
      ∀ S : Sylow p G,
        IsCyclic (↥(S : Subgroup G)) →
          ((S : Subgroup G) ⊓ derivedSubgroup G = ⊥) ∨ (S : Subgroup G) ≤ derivedSubgroup G := by
  intro p _hp S hcyc
  simpa [derivedSubgroup] using
    (sylow_inf_commutator_eq_bot_or_le_commutator (G := G) p S hcyc)

-- Corollary 1.19(b)


end
