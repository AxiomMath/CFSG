module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17i
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17ii
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17iii
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970), "On groups with abelian Sylow 2-subgroups" — Section 1 facts

Reference [1] of the dihedral-Sylow project: H. Bender, "On groups with
abelian Sylow 2-subgroups", Math. Z. 117 (1970), 164--176.  The validated
transcription is `refs/bender-abelian-sylow2.tex` (13/13 pages, 32/32
numbered statements).  Section 1 (Introduction, pp. 164--167) contains the
statements 1.1--1.9.

This file is the statement wrapper for the Section-1 facts that the
`GorensteinWalter.Section2` proofs need, per the "Proof blockers ledger" of
`node_graph/section2.md`:

* `bender1970_1_6_maximalSubgroups_pGroups` — Statement 1.6;
* `bender1970_1_7_i_oddCoreDisjoint`, `bender1970_1_7_ii_commutator_pResidual`,
  `bender1970_1_7_iii_equalityOfMaximal` — Statement 1.7(i)--(iii);
* `bender1970_1_8_centralizerNormalizer_pGroup`,
  `bender1970_1_9_centralizer_pGroup` — Statements 1.8 and 1.9.

The `O_q` / `O_π` / `O^p` / `π`-notation API and the Thompson lemma 1.1 live
in the lower module `GorensteinWalter.Section2.Bender1970API` (imported
above).  The per-statement proofs live in the modules
`Bender1970_16`, `Bender1970_17i`, `Bender1970_17ii`, `Bender1970_17iii`,
`Bender1970_18`, `Bender1970_19`.  This wrapper imports the landed proofs of
Statements 1.6--1.9.

Statement 1.7(iv) and (v) are NOT translated: (iv) needs the paper's notion
of an `A^*`-group (a normal series `1 ⊆ N ⊆ M ⊆ G` with `N` and `G/M`
solvable of odd order and `M/N` a direct product of a 2-group with simple
groups of type `L_2(q)` or JR), which has no formal counterpart in the
repository (JR-type groups and `PΓL(2,q)` are not available); (v) is derived
from (iv) in the paper.  The ledger's pin of 1.7 quotes only (i) and (ii).

Note on the ledger's "[1, 1.10]" citation (`theorem_2_6` row): the paper [1]
has no statement 1.10 — its Section 1 is exactly 1.1--1.9 (verified 13/13
pages, statement inventory in `node_graph/review-bender-abelian-sylow2-tex.md`).
The ledger's "1.1(ii/iii/iv)", "1.6", "1.7", "1.10" citations in the
`theorem_2_6` and `lemma_2_9` rows refer to Section 1 of the *dihedral* paper
(`books/bender-dihedral-sylow.pdf`, pp. 217--218), i.e. D-group facts taken
from Gorenstein--Walter, which are not statements of [1].  The transcription
wins: the closest [1] facts of that kind are 1.8 and 1.9, translated below.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u v

/-! ## Statement 1.7: a subnormal subgroup of `F^*(A)` inside a subgroup `B`

Bender [1], Statement 1.7 (pp. 166--167): let `A` be a maximal subgroup of a
simple group `G`, `S` a subnormal subgroup of `F^*(A)` with
`C_{F^*(A)}(S) ⊆ S`, and `S ⊆ B ⊆ G`.  The three translated items are:
(i) `O_q(B) ∩ A = 1` for `q ∉ π(F(A))`; (ii) `[O_p(B), O^p(F^*(A))] = 1` for
`p ∈ π(F(A))`; (iii) if `B` is maximal and `|π(F^*(A))| ≥ 2` or
`|π(F^*(B))| ≥ 2`, then `A = B` as soon as `A` contains a subnormal subgroup
`Sbar` of `F^*(B)` with `C_{F^*(B)}(Sbar) ⊆ Sbar`.  Items (iv) and (v) are
not translated (they need the paper's `A^*`-group notion; see the module
header).
-/

end CFSG.GorensteinWalter
