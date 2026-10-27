module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremA
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma7_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman Theorem D (the normal `p`-complement criterion)

Proof of Theorem D of George Glauberman, *A Characteristic Subgroup of a p-Stable
Group*, Canadian Journal of Mathematics 20 (1968), 1101–1135 — reference [6] of the
dihedral-Sylow project — following the validated transcription in
`refs/glauberman-p-stable.tex` (Theorem D at L330–L334, proof at L1972–L1989).

The target statement is exactly the wrapper's `Glauberman.theoremD`:

```lean
theorem theoremD {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) :
    NormalPComplement p G ↔
      NormalPComplement p
        (↥(Subgroup.normalizer ((ZJ (G := G) S.toSubgroup : Subgroup G) : Set G)))
```

The forward direction is proved here in full: a normal `p`-complement descends to
every subgroup, in particular to `N_G(Z(J(S)))`.

The backward direction is reduced to the exact Thompson-method bridge recorded in
`/tmp/glauberman-d-report.md`.  The source proof (tex L1972–L1989) derives, in a
minimal counterexample, the data

* `C_G(O_p(G)) ⊆ O_p(G)`,
* `G` solvable,
* a prime `q ≠ p` with Abelian Sylow `q`-subgroups and `π(G) = {p,q}`;

then uses `p` odd + Abelian Sylow 2 to exclude `Qd(p)`, Lemma 6.3 for `p`-stability,
and Theorem A for `Z(J(S)) ⊴ G`.  The part proved in this module takes the resulting
data `C_G(O_p(G)) ⊆ O_p(G)` and `¬ Involved (Qd p) G` (the exact content of
`ThompsonData` below) and completes the contradiction through Theorem A and the
normal-`p`-complement APIs.  No `sorry`/`axiom`/`opaque` is used in this file.
-/

open scoped Pointwise

namespace CFSG.Glauberman

universe u

/-! ## Conversion between the two normal-`p`-complement predicates -/

/-- Convert Glauberman's `O_{p',p}(G) = G` convention to the transfer-API
existential convention. -/
private theorem hasNormalPComplement_of_normalPComplement
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (h : NormalPComplement p G) : HasNormalPComplement p G := by
  classical
  let Q := G ⧸ pPrimeCore p G
  let q : G →* Q := QuotientGroup.mk' (pPrimeCore p G)
  have hOp : Op_p'p p G = ⊤ := normalPComplement_eq_top h
  have hcomap : (pCore p Q).comap q = ⊤ := by
    simpa [Op_p'p, Q, q] using hOp
  have hpcore : pCore p Q = ⊤ := by
    calc
      pCore p Q = ((pCore p Q).comap q).map q := by
        rw [Subgroup.map_comap_eq_self_of_surjective (f := q)
          (QuotientGroup.mk'_surjective (pPrimeCore p G)) (pCore p Q)]
      _ = (⊤ : Subgroup G).map q := by rw [hcomap]
      _ = ⊤ := by
        exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective (pPrimeCore p G))
  have hqtop : IsPGroup p (⊤ : Subgroup Q) := by
    rw [← hpcore]
    exact pCore_isPGroup (G := Q) (p := p)
  have hQp : IsPGroup p Q := hqtop.of_equiv Subgroup.topEquiv
  exact ⟨pPrimeCore p G, inferInstance, pPrimeCore_coprime_card (G := G) (p := p), hQp⟩

/-- Convert the transfer-API existential convention back to Glauberman's
`O_{p',p}(G) = G` convention. -/
private theorem normalPComplement_of_hasNormalPComplement
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (h : HasNormalPComplement p G) : NormalPComplement p G := by
  let Q := G ⧸ pPrimeCore p G
  have hq : IsPGroup p Q :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) G h
  have hqtop : IsPGroup p (⊤ : Subgroup Q) := hq.to_subgroup ⊤
  have hpcore : pCore p Q = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, hqtop⟩
  apply normalPComplement_of_eq_top
  simp [Op_p'p, Q, hpcore]

/-! ## The forward direction of Theorem D -/

/-- A normal `p`-complement of `G` descends to the subgroup `H ≤ G`. -/
private theorem normalPComplement_of_subgroup
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (h : NormalPComplement p G) :
    NormalPComplement p (↥H) := by
  have hG : HasNormalPComplement p G := hasNormalPComplement_of_normalPComplement h
  have hTop : HasNormalPComplement p (↥(⊤ : Subgroup G)) :=
    hasNormalPComplement_of_equiv (G := G) (G' := ↥(⊤ : Subgroup G)) p
      (Subgroup.topEquiv (G := G)).symm hG
  have hH : HasNormalPComplement p (↥H) :=
    hasNormalPComplement_of_le (G := G) (p := p) (K := H) (L := ⊤) le_top hTop
  exact normalPComplement_of_hasNormalPComplement hH

/-! ## The Thompson bridge and the backward reduction -/

/-- The exact data supplied by Thompson's method in a minimal counterexample to the
backward direction of Theorem D ([6], proof of Theorem D, tex L1974–L1983):
`C_G(O_p(G)) ⊆ O_p(G)`, `G` is solvable, and for some prime `q ≠ p` the Sylow
`q`-subgroups are Abelian while `p` and `q` are the only prime divisors of `|G|`.

This is the unformalized transfer lemma; its proof is external to this module
(Thompson's method, cited from Thompson pp. 43–44).  The exact Lean statement is
recorded in `/tmp/glauberman-d-report.md`. -/
private def ThompsonMethodData (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] : Prop :=
  Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) ≤ pCore p G ∧
    IsSolvable G ∧
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧
      (∀ T : Sylow q G, IsMulCommutative (T : Subgroup G)) ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p ∨ r = q

/-- The two Thompson-method consequences actually needed to close Theorem D:
self-centralizing `O_p(G)` and exclusion of `Qd(p)`.  The second follows from the
`ThompsonMethodData` prime structure and `p ≠ 2` via the (independent, not yet
formalized here) `Qd_not_involved_of_abelian_sylow_two` subnode. -/
private def ThompsonData (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] : Prop :=
  Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) ≤ pCore p G ∧
    ¬ Involved (Qd p) G

/-- From `¬ Involved (Qd p) G` (odd `p`), every element of `M_p(G)` is `p`-stable:
apply Lemma 6.3 to each `M ∈ M_p(G)` and use `O_p(M) ≠ 1` to pass from global
stability to the local condition. -/
private theorem pStable_of_not_involved
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type u} [Group G] [Finite G]
    (hInv : ¬ Involved (Qd p) G) : pStable p G := by
  intro M hM
  have hMp : pCore p (↥M) ≠ ⊥ := hM.1
  have hInvM : ¬ Involved (Qd p) (↥M) := by
    intro h
    exact hInv (involved_of_involved_subgroup h)
  have hquot := (lemma6_3 (p := p) hpodd (G := ↥M)).1 hInvM
  have hstableTop :
      pStable p (↥(⊤ : Subgroup (↥M)) ⧸ (⊥ : Subgroup (↥(⊤ : Subgroup (↥M))))) :=
    hquot (⊤ : Subgroup (↥M)) (⊥ : Subgroup (↥(⊤ : Subgroup (↥M))))
  have hstableM : pStable p (↥M) := by
    simpa using
      ((pStable_iso (G := ↥(⊤ : Subgroup (↥M)) ⧸ (⊥ : Subgroup (↥(⊤ : Subgroup (↥M)))))
        (G' := ↥M)
        ((QuotientGroup.quotientBot (G := ↥(⊤ : Subgroup (↥M)))).trans
          (Subgroup.topEquiv (G := ↥M)))).1 hstableTop)
  exact pStableLocal_of_core_ne_bot (G := ↥M) p hstableM hMp

/-- The backward direction of Theorem D, reduced to `ThompsonData`.  Theorem A makes
`Z(J(S))` characteristic (hence normal), so its normalizer is `G`, and the given
normal `p`-complement of the normalizer becomes one of `G`. -/
public theorem theoremD_of_thompsonData {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {G : Type u} [Group G] [Finite G] (S : Sylow p G)
    (hdata : Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) ≤ pCore p G ∧
      ¬ Involved (Qd p) G) :
    NormalPComplement p
        (↥(Subgroup.normalizer ((ZJ (G := G) S.toSubgroup : Subgroup G) : Set G))) →
      NormalPComplement p G := by
  rcases hdata with ⟨hC, hInv⟩
  intro hN
  have hstab : pStable p G := pStable_of_not_involved hpodd hInv
  let Z : Subgroup G := ZJ (G := G) S.toSubgroup
  have hZchar : Z.Characteristic :=
    Glauberman.TheoremA.theoremA hpodd S hstab hC
  haveI : Z.Characteristic := hZchar
  have hZnorm : Z.Normal := inferInstance
  have hNtop : Subgroup.normalizer (Z : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hZnorm
  have hNequiv : ↥(Subgroup.normalizer (Z : Set G)) ≃* G :=
    (MulEquiv.subgroupCongr hNtop).trans (Subgroup.topEquiv (G := G))
  have hcompN : HasNormalPComplement p (↥(Subgroup.normalizer (Z : Set G))) :=
    hasNormalPComplement_of_normalPComplement hN
  have hcompG : HasNormalPComplement p G :=
    hasNormalPComplement_of_equiv (G := ↥(Subgroup.normalizer (Z : Set G))) (G' := G)
      p hNequiv hcompN
  exact normalPComplement_of_hasNormalPComplement hcompG


end CFSG.Glauberman
