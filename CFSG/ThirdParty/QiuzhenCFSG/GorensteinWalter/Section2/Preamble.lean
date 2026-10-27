module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1 -- fact_1_4_*, fact_1_5_iii, centralizerIn, sqrtOf

namespace CFSG
end CFSG
open CFSG

/-!
# Section 2 preamble-fact proofs

Bender, "Finite Groups with Dihedral Sylow 2-Subgroups", J. Algebra 70 (1981),
p. 219.  The section preamble recalls three facts from Gorenstein--Walter
[10]: (1) all involutions of `G` are conjugate, (2) `H` is `S·U`, and
(3) `N_G(V)` is transitive on `V^#` for every `V = (2,2) ≤ S`.  The first two
are the statements `fact_2_preamble_involutions_conjugate` and
`fact_2_preamble_H_eq_SU` in `GorensteinWalter/Section2/Basic.lean`; the third
is recorded as a gap in `node_graph/section2.md`.

The involution-conjugacy fact is now locally assembled in
`GorensteinWalter.Section2.PreambleInvolutions`: simplicity excludes the
index-two branch of the translated Gorenstein--Walter Lemma 2.1, while its
normal-`2`-complement branch contradicts minimality.  Its upstream source
interfaces still carry `sorryAx`.  The equality `H = S ⊔ O(H)` is proved by
restricting `S` to a Sylow `2`-subgroup of `H`, applying
`properSubgroups_areDGroups` to `H`, eliminating the `A₇`, `PSL₂`, and `PGL₂`
branches using a surviving central involution and trivial-center theorems,
and lifting the resulting `2`-group quotient statement.  The proof and reusable
setup theorem `centralizerSetup_S_le_H` live in the lower acyclic module
`GorensteinWalter.Section2.PreambleHSU`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

-- ============================================================================
-- LOCALLY PROVED: fact_2_preamble_involutions_conjugate
-- (`GorensteinWalter/Section2/Basic.lean`, p. 219:
--  "We recall that all involutions of G are conjugate")
--
-- `IsMinimalCounterexample` (GorensteinWalter/Classification.lean:90) is
-- `HasDihedralSylowTwo G ∧ ¬ IsDGroup G ∧` the order-minimality clause; the
-- one-involution-class property is NOT part of the hypothesis, so this is not
-- a projection.  The paper does not prove it either; it is recalled from
-- [10], where it follows from
--   (i) the minimal counterexample is simple — [10, Prop 9],
--       `minimalCounterexample_isSimple` (locally assembled in
--       `GorensteinWalter/MinimalCounterexample.lean`, with upstream
--       Proposition-9 `sorryAx` dependencies), and
--   (ii) [10, Fact 1.6] (paper p. 218): in a group with dihedral or cyclic
--        Sylow 2-subgroups, if `O^2(G) = G` then all involutions of `G` are
--        conjugate.  A simple `G` satisfies `O^2(G) = G`.  Fact 1.6 is the
--        four-case Gorenstein--Walter structure theorem for groups with
--        dihedral or cyclic Sylow 2-subgroups (paper p. 217-218); its proof
--        is the classification of simple groups with dihedral Sylow
--        2-subgroups (`G ≅ PSL(2,q)` or `A₇`, where all involutions are
--        conjugate) — not formalized in this repository, and it is exactly
--        the theorem this paper is proving.
--
-- The exported statement is:
--
--   theorem fact_2_preamble_involutions_conjugate
--       {G : Type u} [Group G] [Finite G]
--       (hmin : IsMinimalCounterexample G) :
--       ∀ x y : G, IsInvolution x → IsInvolution y → ∃ g : G, g * x * g⁻¹ = y
--
-- The local proof now consumes the translated `gw_lemma_2_1`, which packages
-- the needed Fact 1.6 consequence.  That interface remains an upstream
-- source-level `sorry`, so the exported theorem is not yet axiom-free.
-- The underlying structure theorem ([10, Fact 1.6], in repo notation) is:
--
--   theorem gw_1_6_involutions_conjugate_of_twoResidual
--       {G : Type u} [Group G] [Finite G]
--       (hSylow : HasCyclicOrDihedralSylowTwo G)
--       (hO2 : twoResidualOf (⊤ : Subgroup G) = ⊤) :
--       ∀ x y : G, IsInvolution x → IsInvolution y → ∃ g : G, g * x * g⁻¹ = y
--
-- (`twoResidualOf` is `O^2` in repo notation, Defs.lean:37.)
-- The proof lives in `GorensteinWalter.Section2.PreambleInvolutions`.
-- ============================================================================

-- ============================================================================
-- PROVED: fact_2_preamble_H_eq_SU
-- (`GorensteinWalter/Section2/Basic.lean`, p. 219:
--  "We recall that ... H is SU")
--
-- The proof is in `GorensteinWalter.Section2.PreambleHSU`.  Its key route is
-- `S ≤ H`; restriction of the ambient Sylow subgroup to `H`; a nontrivial
-- central involution surviving in `H/O(H)`; `properSubgroups_areDGroups` for
-- the proper subgroup `H`; elimination of the `A₇`, `PSL₂`, and `PGL₂`
-- branches by their trivial centers; and the Sylow-plus-kernel generation
-- lemma for the resulting `2`-group quotient.  Mapping the equality from the
-- subtype `H` back to `G` gives `(c.S : Subgroup G) ⊔ c.U = c.H`.
-- ============================================================================

/-! The reusable setup theorem `centralizerSetup_S_le_H` and the full
`H = S ⊔ O(H)` proof now live in the lower acyclic module
`GorensteinWalter.Section2.PreambleHSU`, imported by `Basic.lean`. -/

end CFSG.GorensteinWalter
