module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_17

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Theorem 1.18
**Stmt**:
Let $G$ be a finite group.
Let $p$ be a prime.
Let $S$ be a Sylow $p$-subgroup of $G$.
Let $S \subset Z(N_G(S))$.
Then $G$ has a normal $p$-complement.
-/

public theorem CFSG.hasNormalPComplement_of_sylow_le_center_normalizer
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (S : Sylow p G)
    (hS : (S : Subgroup G) ≤ centerIn (G := G) (Subgroup.normalizer (S : Subgroup G))) :
    HasNormalPComplement p G := by
  simpa [HasNormalPComplement] using
    (exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer
      (G := G) p S hS)

public theorem CFSG.theorem_1_18 {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (S : Sylow p G)
    (hS : (S : Subgroup G) ≤ centerIn (G := G) (Subgroup.normalizer (S : Subgroup G))) :
    HasNormalPComplement p G := by
  exact hasNormalPComplement_of_sylow_le_center_normalizer (G := G) p S hS


end
