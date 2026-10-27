module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.corollary_1_12

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Proposition 1.15
**Stmt**:
Let `G` be a finite solvable group.
Let `p` be a prime.
(a) If `T` is a Sylow `p`-subgroup of `𝒪_{p',p}(G)`. Then `C_G(T) ⊂ 𝒪_{p',p}(G)`.
(b) If `R` is a `p`-subgroup of `G`. Then `𝒪_{p'}(C_G(R)) ⊂ 𝒪_{p'}(G)`.
-/

public theorem CFSG.proposition_1_15_a {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G) (p : ℕ) [Fact p.Prime] :
    ∀ T : Sylow p (↥(Op_p'p p G)),
      Subgroup.centralizer ((T.1.map (Op_p'p p G).subtype : Subgroup G) : Set G) ≤ Op_p'p p G := by
  exact centralizer_sylow_subgroup_le_op_p_prime_p_of_solvable (G := G) hsolv p

public theorem CFSG.proposition_1_15_b {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G) (p : ℕ) [Fact p.Prime] :
    ∀ R : Subgroup G,
      IsPGroup p (↥R) →
        let C : Subgroup G := Subgroup.centralizer (R : Set G)
        (pPrimeCore p (↥C)).map C.subtype ≤ pPrimeCore p G := by
  exact pPrimeCore_map_centralizer_le_pPrimeCore_of_solvable (G := G) hsolv p


end
