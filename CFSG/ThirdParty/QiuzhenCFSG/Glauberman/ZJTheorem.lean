module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremA
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — Theorems A–D and Lemma 6.3

The final statements of Glauberman's paper, transcribed from George Glauberman,
*A Characteristic Subgroup of a p-Stable Group*, Canadian Journal of Mathematics 20
(1968), 1101–1135 — reference [6] of the dihedral-Sylow project — following the validated
transcription in `refs/glauberman-p-stable.tex`.

The §2 definitions used by these statements live in `Glauberman/Definitions.lean`; this
module is the wrapper where the main theorems are assembled.  This is the input for
`GorensteinWalter.Section2.Basic.lemma_2_4` and `BenderGlauberman/Section2/Basic.lean`:
Theorem A (the ZJ-theorem), Theorem B, and Lemma 6.3 (see the ledger rows in
`node_graph/section2.md` and `node_graph/bg_section2.md`).  Theorems C and D are included
for completeness of the statement section (§2 of the paper).

Modified for CFSG: `theoremD` is removed. Its proof was `sorry` upstream and nothing here
uses it.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

/-! ## The main theorems (paper §2) -/

/-- Glauberman's Theorem A (the ZJ-theorem): if `p` is an odd prime, `S` is a Sylow
`p`-subgroup of the finite group `G`, `G` is `p`-stable, and `C(O_p(G)) ⊆ O_p(G)`, then
`Z(J(S))` is a characteristic subgroup of `G` ([6], §2, Theorem A, p. 1105: "Let `p` be
an odd prime, and let `S` be a Sylow `p`-subgroup of a finite group `G`. Assume that `G`
is `p`-stable and that `C(O_p(G)) ⊆ O_p(G)`. Then `Z(J(S))` is a characteristic subgroup
of `G`").  This is the "Glauberman ZJ-theorem" applied by
`GorensteinWalter.Section2.Basic.lemma_2_4` and `BenderGlauberman/Section2/Basic.lean`
(see `node_graph/section2.md`, `node_graph/bg_section2.md`). -/
public theorem theoremA {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) :
    pStable p G → Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) ≤ pCore p G →
      (ZJ (G := G) S.toSubgroup).Characteristic := by
  exact Glauberman.TheoremA.theoremA hpodd (G := G) S

/-! ## Lemma 6.3: sorry-free partial infrastructure -/

/-- The sorry-free `(b) ⟹ (a)` direction of Lemma 6.3: if every subquotient of `G` is
`p`-stable, then `Qd(p)` is not involved in `G`.  An involvement witness
`K ⧸ N ≃ Qd(p)` gives `pStable (Qd p)` by `pStable_iso`, contradicting the
sorry-free `qd_not_pStable` (proved in `Glauberman/Lemma6_3.lean`). -/
private theorem lemma_6_3_backward {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*}
    [Group G]
    (hb : ∀ (K : Subgroup G) (N : Subgroup K) [_hN : N.Normal], pStable p (K ⧸ N)) :
    ¬ Involved (Qd p) G := by
  intro hInv
  rcases hInv with ⟨K, N, hN, hq⟩
  let : N.Normal := hN
  rcases hq with ⟨e⟩
  have hstab : pStable p (K ⧸ N) := hb K N
  have hqd : pStable p (Qd p) := (pStable_iso (G := K ⧸ N) (G' := Qd p) e).1 hstab
  exact qd_not_pStable hpodd hqd

/-- The `(a) ⟹ (b)` direction of Lemma 6.3 abstracted over its
minimal-counterexample implication. -/
private theorem lemma_6_3_forward_of_qd_involved {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G]
    (hbridge : (∃ (K : Subgroup G) (N : Subgroup K) (hN : N.Normal),
      letI : N.Normal := hN; ¬ pStable p (K ⧸ N)) → Involved (Qd p) G)
    (hInv : ¬ Involved (Qd p) G) :
    ∀ (K : Subgroup G) (N : Subgroup K) [_hN : N.Normal], pStable p (K ⧸ N) := by
  classical
  intro K N _hN
  let : N.Normal := _hN
  by_contra h
  exact hInv (hbridge ⟨K, N, _hN, h⟩)

/-- Lemma 6.3 assembled from its backward direction and an abstract
minimal-counterexample implication. -/
private theorem lemma_6_3_of_qd_involved {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {G : Type*} [Group G] [Finite G]
    (hbridge : (∃ (K : Subgroup G) (N : Subgroup K) (hN : N.Normal),
      letI : N.Normal := hN; ¬ pStable p (K ⧸ N)) → Involved (Qd p) G) :
    (¬ Involved (Qd p) G) ↔
      ∀ (K : Subgroup G) (N : Subgroup K) [N.Normal], pStable p (K ⧸ N) := by
  constructor
  · exact lemma_6_3_forward_of_qd_involved hbridge
  · exact lemma_6_3_backward hpodd

/-- Glauberman's Lemma 6.3 ([6], §6, p. 1122): for an odd prime `p` and a finite group
`G`, `Qd(p)` is not involved in `G` if and only if every subquotient of `G` is
`p`-stable.  The forward direction (a) ⟹ (b) restricted to `G` itself is the input
needed to apply Theorem A in `GorensteinWalter.Section2.Basic.lemma_2_4` (`Ĥ` is
`p`-stable because `Qd(p)` is not involved in it).  The proof is fully transcribed in
`refs/glauberman-p-stable.tex` L1664–L1793 (minimal non-`p`-stable subquotient is
isomorphic to `Qd(p)`). -/
public theorem lemma_6_3 {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] :
    (¬ Involved (Qd p) G) ↔
      ∀ (K : Subgroup G) (N : Subgroup K) [_hN : N.Normal], pStable p (K ⧸ N) := by
  exact lemma6_3 hpodd

end CFSG.Glauberman
