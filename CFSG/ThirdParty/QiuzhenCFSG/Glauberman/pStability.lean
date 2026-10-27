module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Commutator.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Shared plumbing for the `pStable`/`pStableLocal` conditions

This module provides the shared infrastructure used to *apply* the `pStableLocal`/`pStable`
conditions of `Glauberman/ZJTheorem.lean` in the proofs of the round-1 leaves of the
dependency DAG (Theorem A, Lemma 7.2, Lemma 6.3):

* `pCore_quotient_centralizer_le_of_centralizer_le_core` — the claim
  `O_p(G/C_G(P)) ⊆ P·C_G(P)/C_G(P)` for `P = O_p(G)` with `C_G(P) ⊆ P`; this is exactly the
  computation `ZC(P)/C(P) ⊆ O_p(G/C(P)) = P/C(P)` of the proof of Theorem A
  (`refs/glauberman-p-stable.tex` L974–L989, where the right-hand side is written `P/C(P)`).
* `commutator_commutator_eq_bot_of_abelian_normal` — `[P, Z, Z] = 1` whenever `Z ⊴ G` is
  Abelian, used in the Theorem A proof (`refs/glauberman-p-stable.tex` L977–L978:
  "Since `Z` is an Abelian normal subgroup of `S`, then `[P,Z,Z] = 1`").  The variant
  `commutator_commutator_eq_bot_of_abelian_normalizer` covers the hypothesis the paper
  actually has at that point — `Z` Abelian and `P ≤ N_G(Z)` (no normality of `Z` in all of
  `G`) — together with `le_normalizer_of_normal_subgroupOf_of_le`, which supplies
  `P ≤ N_G(Z)` from `Z ⊴ S`, `P ≤ S` (Theorem-A route, review finding F1).
* `commutator_zpowers_le_of_mem` — the element form `[P, x, x] = 1` follows from the
  subgroup form `[P, Z, Z] = 1` for `x ∈ Z`; this connects the paper's `[P,x,x] = 1`
  (Definition 2.1, `refs/glauberman-p-stable.tex` L243) with the subgroup notation.
* `pStableLocal_apply_of_core_normal` — the Theorem-A application shape: when `O_p(G) ≠ 1`
  and `G` is `p`-stable, an element `x` with `[P,x,x] = 1` (`P = O_p(G)`) has its coset
  modulo `C_G(P)` in `O_p(G/C_G(P))`, with no normalizer quotient in sight (the normalizer
  is all of `G` because `P ⊴ G`).  This is the formal content of the step
  "Since `G` is `p`-stable and `C(P) ⊆ P`, we have that `ZC(P)/C(P) ⊆ O_p(G/C(P))`"
  (`refs/glauberman-p-stable.tex` L974–L979) once the first two lemmas above have reduced
  the hypothesis to the `[P,x,x] = 1` condition of Definition 2.1.

All four statements are proved without `axiom`/`opaque`/`sorry`.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-! ## The centralizer commutes with group isomorphisms -/

/-- The centralizer of a subgroup is transported along a group isomorphism: for
`e : G ≃* G'` and `P ≤ G`, one has `C_G(P)ᵉ = C_{G'}(Pᵉ)`.  Used to move the
`pStableLocal` conclusion between the group `G` and its isomorphic copy `↥(⊤ : Subgroup G)`. -/
public theorem map_centralizer_eq_of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (P : Subgroup G) :
    (Subgroup.centralizer (P : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
  refine le_antisymm ?_ ?_
  · simpa [Subgroup.coe_map] using
      (Subgroup.map_centralizer_le_centralizer_image (s := (P : Set G)) (f := e.toMonoidHom))
  · intro y hy
    refine ⟨e.symm y, ?_, ?_⟩
    · intro h hh
      have hy' := hy (e h) (by exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
      apply e.injective
      rw [map_mul, map_mul]
      simp [hy']
    · simp

/-! ## Lemma A: `O_p(G/C_G(P)) ⊆ P·C_G(P)/C_G(P)` when `C_G(P) ⊆ P = O_p(G)` -/

/-- If `C := C_G(P)` is contained in `P := O_p(G)`, then `O_p(G/C) ⊆ P·C/C`, i.e. the
`p`-core of the quotient `G/C` is contained in the image of `P` under the quotient map
([6], Theorem A, proof, `refs/glauberman-p-stable.tex` L974–L989: "Since `G` is `p`-stable
and `C(P) ⊆ P`, we have that `ZC(P)/C(P) ⊆ O_p(G/C(P)) = P/C(P)`"; the equality
`O_p(G/C(P)) = P/C(P)` is exactly this lemma applied to `P = O_p(G)`).

The argument: let `X` be the preimage of `O_p(G/C)` in `G`.  Then `X ⊴ G` and
`X/C ≅ O_p(G/C)` is a `p`-group.  Every Sylow `q`-subgroup `Q` of `X` (`q ≠ p`) maps into
`C`: the image of `Q` in `G/C` is both a `q`-group and a subgroup of the `p`-group
`O_p(G/C)`, hence is trivial, so `Q ≤ ker(G → G/C) = C`.  Since `C ≤ P` and `P` is a
`p`-group, `C` is a `p`-group; therefore no prime `q ≠ p` divides `|X|` (else `X` would
contain a non-trivial `q`-Sylow subgroup, which must lie in `C`, a `p`-group — a
contradiction).  Hence `X` is a `p`-group, so `X ≤ O_p(G) = P`, and mapping down to `G/C`
gives `O_p(G/C) = X/C ≤ P/C`.  The hypothesis `C ≤ P` is essential: without it the
statement is false (e.g. `G = A₄ × S₃ × C₃` for `p = 3`: `P = 1 × A₃ × C₃`,
`C_G(P) = A₄ × A₃ × C₃ ⊄ P`, yet `O₃(G/C) ≠ 1` while `P·C/C = 1`). -/
public theorem pCore_quotient_centralizer_le_of_centralizer_le_core {G : Type*} [Group G]
    [Finite G] (p : ℕ) [Fact p.Prime]
    (h : Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) ≤ pCore p G) :
    pCore p (G ⧸ Subgroup.centralizer ((pCore p G : Subgroup G) : Set G)) ≤
      (pCore p G).map (QuotientGroup.mk' (Subgroup.centralizer ((pCore p G : Subgroup G) : Set G))) := by
  classical
  let P : Subgroup G := pCore p G
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have : C.Normal := Subgroup.normal_centralizer (H := P)
  let mk : G →* G ⧸ C := QuotientGroup.mk' C
  let O : Subgroup (G ⧸ C) := pCore p (G ⧸ C)
  -- `X` = preimage of `O_p(G/C)` under the quotient map
  let X : Subgroup G := O.comap mk
  have hXmap : X.map mk = O :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) O
  have hXnormal : X.Normal := Subgroup.Normal.comap (pCore_normal (G := G ⧸ C)) mk
  -- `X` is a `p`-group: no prime `q ≠ p` divides `|X|`.
  have hXp : IsPGroup p X := by
    rw [IsPGroup.iff_card]
    refine ⟨(Nat.card (↥X)).primeFactorsList.length, ?_⟩
    apply Nat.eq_prime_pow_of_unique_prime_dvd
    · have : Finite (↥X) := inferInstance
      exact ne_of_gt ((Finite.card_pos_iff (α := ↥X)).mpr ⟨⟨1, X.one_mem⟩⟩)
    · intro d hd hdvd
      by_contra hdp
      have hpd : p ≠ d := fun h => hdp h.symm
      let : Fact d.Prime := ⟨hd⟩
      -- a non-trivial Sylow `d`-subgroup `Q` of `X`
      obtain ⟨Q, hQne⟩ : ∃ Q : Sylow d (↥X), (Q : Subgroup (↥X)) ≠ ⊥ := by
        refine ⟨Classical.choice Sylow.nonempty, ?_⟩
        exact Sylow.ne_bot_of_dvd_card (Classical.choice Sylow.nonempty) hdvd
      let K : Subgroup (G ⧸ C) := (Q.map X.subtype).map mk
      have hQleX : Q.map X.subtype ≤ X := by
        intro y hy
        rcases (Subgroup.mem_map.mp hy) with ⟨q, hq, rfl⟩
        exact q.2
      -- the image of `Q` in `G/C` is both a `d`-group and a `p`-group, hence trivial
      have hK_le_O : K ≤ O := by
        exact (Subgroup.map_mono (f := mk) hQleX).trans (le_of_eq hXmap)
      have hK_p : IsPGroup p K := IsPGroup.to_le (pCore_isPGroup (G := G ⧸ C)) hK_le_O
      have hK_q : IsPGroup d K := IsPGroup.map (IsPGroup.map Q.isPGroup' X.subtype) mk
      have hK_bot : K = ⊥ := by
        have hdisj : Disjoint K K := IsPGroup.disjoint_of_ne p d hpd K K hK_p hK_q
        refine le_antisymm ?_ bot_le
        intro y hy
        simpa using (Subgroup.disjoint_def.mp hdisj) hy hy
      -- so `Q ⊆ C`
      have hQleC : Q.map X.subtype ≤ C := by
        intro y hy
        have hyK : mk y ∈ K := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
        rw [hK_bot] at hyK
        exact (QuotientGroup.ker_mk' (N := C) ▸ (MonoidHom.mem_ker (f := mk)).mp (by simpa using hyK))
      -- `C` is a `p`-group (`C ≤ P`), so `Q` is both a `d`-group and a `p`-group:
      -- contradiction with `Q ≠ ⊥`.
      have hQ_p : IsPGroup p (Q.map X.subtype) :=
        IsPGroup.to_le (pCore_isPGroup (G := G)) (hQleC.trans h)
      have hQ_q : IsPGroup d (Q.map X.subtype) := IsPGroup.map Q.isPGroup' X.subtype
      have hQne' : Q.map X.subtype ≠ ⊥ := by
        intro hbot
        apply hQne
        apply (Subgroup.map_injective (f := X.subtype) X.subtype_injective)
        simpa using hbot
      have hdisj2 : Disjoint (Q.map X.subtype) (Q.map X.subtype) :=
        IsPGroup.disjoint_of_ne p d hpd (Q.map X.subtype) (Q.map X.subtype) hQ_p hQ_q
      exact hQne' (le_antisymm (by
        intro y hy
        simpa using (Subgroup.disjoint_def.mp hdisj2) hy hy) bot_le)
  -- `X` is a normal `p`-subgroup of `G`, hence `X ≤ O_p(G)`
  have hXle : X ≤ P := le_sSup ⟨hXnormal, hXp⟩
  calc
    pCore p (G ⧸ C) = X.map mk := hXmap.symm
    _ ≤ P.map mk := Subgroup.map_mono hXle

/-! ## Lemma B: `[P, Z, Z] = 1` for `Z ⊴ G` Abelian -/

/-- If `Z` is an Abelian normal subgroup of `G`, then `⁅⁅P, Z⁆, Z⁆ = ⊥` for every subgroup
`P ≤ G`.  This is the content of the first line of the proof of Theorem A
(`refs/glauberman-p-stable.tex` L977–L978: "Since `Z` is an Abelian normal subgroup of `S`,
then `[P,Z,Z] = 1`"): normality of `Z` gives `[P,Z] ⊆ Z` (each commutator `[p,z]` lies in
`Z` because `p⁻¹z⁻¹p ∈ Z`), and Abelian-ness gives `[Z,Z] = 1`. -/
public theorem commutator_commutator_eq_bot_of_abelian_normal {G : Type*} [Group G]
    {P Z : Subgroup G} (hZnorm : Z.Normal) (hZcomm : IsMulCommutative Z) :
    ⁅⁅P, Z⁆, Z⁆ = ⊥ := by
  have : Z.Normal := hZnorm
  have hPZ : ⁅P, Z⁆ ≤ Z := Subgroup.commutator_le_right (H₁ := P) (H₂ := Z)
  have hZZ : ⁅Z, Z⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hZcomm
  have hle : ⁅⁅P, Z⁆, Z⁆ ≤ ⁅Z, Z⁆ := Subgroup.commutator_mono hPZ le_rfl
  rw [hZZ] at hle
  exact le_bot_iff.mp hle

/-- Variant of `commutator_commutator_eq_bot_of_abelian_normal` with the hypotheses the paper
actually has at the point of Theorem A's first line: `Z` is Abelian and `P` normalizes `Z`
(no normality of `Z` in all of `G`).  This covers the case `Z = Z(J(S))` with `Z ⊴ S` and
`P = O_p(G) ≤ S` (the review finding F1 of `node_graph/review-*`; `refs/glauberman-p-stable.tex`
L977–L978).  The argument is the same: `p⁻¹z⁻¹p ∈ Z` by `P ≤ N_G(Z)`. -/
public theorem commutator_commutator_eq_bot_of_abelian_normalizer {G : Type*} [Group G]
    {P Z : Subgroup G} (hPZ : P ≤ Subgroup.normalizer (Z : Set G))
    (hZcomm : IsMulCommutative Z) :
    ⁅⁅P, Z⁆, Z⁆ = ⊥ := by
  have hPZ_comm : ⁅P, Z⁆ ≤ Z :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := P) (K := Z)).mp hPZ
  have hZZ : ⁅Z, Z⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hZcomm
  have hle : ⁅⁅P, Z⁆, Z⁆ ≤ ⁅Z, Z⁆ := Subgroup.commutator_mono hPZ_comm le_rfl
  rw [hZZ] at hle
  exact le_bot_iff.mp hle

/-- The normalizer hypothesis of `commutator_commutator_eq_bot_of_abelian_normalizer` holds
when `Z ≤ S`, `Z ⊴ S` and `P ≤ S`: members of `P` normalize `Z` through `S`. -/
public theorem le_normalizer_of_normal_subgroupOf_of_le {G : Type*} [Group G]
    {P Z S : Subgroup G} (hZle : Z ≤ S) (hZS : (Z.subgroupOf S).Normal) (hP : P ≤ S) :
    P ≤ Subgroup.normalizer (Z : Set G) := by
  exact le_trans hP
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (H := Z) (K := S) hZle).1 hZS)

/-! ## Lemma C: from `[P, Z, Z] = 1` to `[P, x, x] = 1` -/

/-- If `⁅⁅P, Z⁆, Z⁆ = ⊥` and `z ∈ Z`, then `⁅⁅P, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥`.
This connects the subgroup formulation of Definition 2.1 (`refs/glauberman-p-stable.tex`
L243: "If `[P,x,x] = 1`") with the element form used in the wrapper's `pStableLocal`. -/
public theorem commutator_zpowers_le_of_mem {G : Type*} [Group G] {P Z : Subgroup G}
    (h : ⁅⁅P, Z⁆, Z⁆ = ⊥) {z : G} (hz : z ∈ Z) :
    ⁅⁅P, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥ := by
  have hzle : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.mpr hz
  have hle : ⁅⁅P, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ ≤ ⁅⁅P, Z⁆, Z⁆ :=
    Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hzle) hzle
  rw [h] at hle
  exact le_bot_iff.mp hle

/-! ## Lemma D: the Theorem-A application shape of `pStable` -/

/-- The Theorem-A application of the `pStable` hypothesis: if `G` is `p`-stable and
`P := O_p(G) ≠ ⊥`, then every `x ∈ G` with `[P,x,x] = 1` has its coset modulo `C_G(P)` in
`O_p(G/C_G(P))`.

Formally: `pStable p G` quantifies over `M ∈ M_p(G)` (Definition 2.3,
`refs/glauberman-p-stable.tex` L243–L247).  Since `P ≠ ⊥`, the subgroup `⊤ ≤ G` lies in
`M_p(G)` (`O_p(⊤) = O_p(G) ≠ ⊥` via the canonical isomorphism `⊤ ≃ G`, and maximality is
trivial), so `G` itself is `p`-stable in the sense of Definition 2.1.  Instantiating with
the `p`-subgroup `P = O_p(G)`: `P ⊴ G` so `N_G(P) = G` and `O_{p'}(G)P ⊴ G`; the commutator
hypothesis is given; and the conclusion `x̄ ∈ O_p(N_G(P)/C_G(P))` is transported from the
normalizer quotient to `G/C_G(P)` along the isomorphism `⊤ ⧸ C.subgroupOf ⊤ ≃* G ⧸ C`
(quotient transport via `QuotientGroup.congr`, `pCore_map_iso`, and
`map_centralizer_eq_of_equiv`).  This is the formal content of the step
`ZC(P)/C(P) ⊆ O_p(G/C(P))` in the proof of Theorem A (`refs/glauberman-p-stable.tex`
L974–L979). -/
public theorem pStableLocal_apply_of_core_normal {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hstab : pStable p G) (hPne : pCore p G ≠ ⊥) :
    let P := pCore p G
    ∀ x : G, ⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ →
      QuotientGroup.mk' (Subgroup.centralizer (P : Set G)) x ∈
        pCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
  classical
  intro P x hcomm
  -- `⊤ ∈ M_p(G)` because `O_p(⊤) ≅ O_p(G) ≠ ⊥`
  have hMtop : (⊤ : Subgroup G) ∈ MpSet p G := by
    change pCore p (↥(⊤ : Subgroup G)) ≠ ⊥ ∧
      ∀ K : Subgroup G, pCore p (↥K) ≠ ⊥ → (⊤ : Subgroup G) ≤ K → K = (⊤ : Subgroup G)
    constructor
    · intro hbot
      apply hPne
      have hmap := pCore_map_iso (G := ↥(⊤ : Subgroup G)) (G' := G) (p := p)
        (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G))
      simpa [hbot] using hmap.symm
    · intro K hKne htople
      exact le_antisymm le_top htople
  have hstabTop : pStableLocal p (G := ↥(⊤ : Subgroup G)) := hstab (⊤ : Subgroup G) hMtop
  -- work in the isomorphic copy `T := ↥(⊤ : Subgroup G)` of `G`
  let T := ↥(⊤ : Subgroup G)
  let e : T ≃* G := Subgroup.topEquiv
  have hP0p : IsPGroup p (P.map e.symm.toMonoidHom) :=
    IsPGroup.map (pCore_isPGroup (G := G)) e.symm.toMonoidHom
  have hP0_normal : (P.map e.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map pCore_normal e.symm.toMonoidHom e.symm.surjective
  have hP0n : (pPrimeCore p T ⊔ P.map e.symm.toMonoidHom).Normal := by
    have hp' : pPrimeCore p T = (pPrimeCore p G).map e.symm.toMonoidHom := by
      exact (pPrimeCore_map_iso (G := G) (G' := T) (p := p) (f := e.symm)).symm
    rw [hp']
    dsimp
    rw [← Subgroup.map_sup (pPrimeCore p G) P (e.symm : G →* T)]
    exact Subgroup.Normal.map (Subgroup.sup_normal (pPrimeCore p G) P) e.symm.toMonoidHom
      e.symm.surjective
  let x0 : T := ⟨x, by simp⟩
  have hx0 : x0 ∈ Subgroup.normalizer ((P.map e.symm.toMonoidHom) : Set T) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hP0_normal]
    trivial
  -- the commutator hypothesis in `G` transports to `T`
  have hP0_map : (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
    dsimp
    have hcomp : (e : T →* G).comp (e.symm : G →* T) = MonoidHom.id G := by
      ext g
      simp
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hZ0_map : (Subgroup.zpowers x0).map e.toMonoidHom = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    congr 1
  have hcomm0 : ⁅⁅P.map e.symm.toMonoidHom, Subgroup.zpowers x0⁆, Subgroup.zpowers x0⁆ = ⊥ := by
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hP0_map, hZ0_map, hcomm,
      Subgroup.map_bot]
  -- the `pStableLocal` conclusion, with `N = N_T(P₀) = ⊤` and `C = C_T(P₀)`
  let N0 : Subgroup T := Subgroup.normalizer ((P.map e.symm.toMonoidHom) : Set T)
  let C0 : Subgroup T := Subgroup.centralizer ((P.map e.symm.toMonoidHom) : Set T)
  have hN0 : N0 = ⊤ := by simpa [N0] using (Subgroup.normalizer_eq_top_iff.mpr hP0_normal)
  have hC0_normal : C0.Normal := Subgroup.normal_centralizer (H := P.map e.symm.toMonoidHom)
  have : (C0.subgroupOf N0).Normal := Subgroup.Normal.subgroupOf hC0_normal N0
  have : (C0.subgroupOf (⊤ : Subgroup T)).Normal :=
    Subgroup.Normal.subgroupOf hC0_normal (⊤ : Subgroup T)
  have hconcl0 : QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩ ∈ pCore p (N0 ⧸ C0.subgroupOf N0) := by
    simpa [N0, C0] using (hstabTop (P.map e.symm.toMonoidHom) hP0p hP0n x0 hx0 hcomm0)
  -- step 1: transport `N0 ⧸ C0.subgroupOf N0` to `⊤ ⧸ C0.subgroupOf ⊤` (ambient `↥⊤`)
  let eN0 : ↥N0 ≃* ↥(⊤ : Subgroup T) :=
    { toEquiv := Equiv.subtypeEquivRight (fun y : T => by rw [hN0])
      map_mul' := by intro a b; rfl }
  have heN0 : (C0.subgroupOf N0).map (eN0 : ↥N0 →* ↥(⊤ : Subgroup T)) =
      C0.subgroupOf (⊤ : Subgroup T) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz)
    · intro hy
      refine ⟨⟨y, by simp [hN0]⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (by simpa using (Subgroup.mem_subgroupOf.mp hy))
      · apply Subtype.ext
        rfl
  let Φ₀ : ↥N0 ⧸ C0.subgroupOf N0 ≃* ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T) :=
    QuotientGroup.congr (G := ↥N0) (H := ↥(⊤ : Subgroup T))
      (G' := C0.subgroupOf N0) (H' := C0.subgroupOf (⊤ : Subgroup T)) eN0 heN0
  have hcore₀ : (pCore p (↥N0 ⧸ C0.subgroupOf N0)).map Φ₀.toMonoidHom =
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) :=
    pCore_map_iso (G := ↥N0 ⧸ C0.subgroupOf N0) (G' := ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T))
      (p := p) (f := Φ₀)
  have hmem₀ : Φ₀ (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩) ∈
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) := by
    rw [← hcore₀]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩, hconcl0, rfl⟩
  have happly₀ : Φ₀ (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩) =
      QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T)) ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩ := by
    dsimp [Φ₀]
    rfl
  have hconcl1 : QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩ ∈
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) := by
    rw [happly₀] at hmem₀
    exact hmem₀
  -- step 2: transport `⊤ ⧸ C0.subgroupOf ⊤` to `G ⧸ C` along `e : T ≃* G`
  have : (Subgroup.centralizer (P : Set G)).Normal := Subgroup.normal_centralizer (H := P)
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let eT : ↥(⊤ : Subgroup T) ≃* T := Subgroup.topEquiv
  let eTot : ↥(⊤ : Subgroup T) ≃* G := eT.trans e
  have he_subgroupOf : (C0.subgroupOf (⊤ : Subgroup T)).map eT.toMonoidHom = C0 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [eT] using (Subgroup.mem_subgroupOf.mp hz)
    · intro hy
      refine ⟨⟨y, by simp⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (by simpa using hy)
      · rfl
  have he_centralizer : C0.map e.toMonoidHom = C := by
    calc
      C0.map e.toMonoidHom =
          Subgroup.centralizer (((P.map e.symm.toMonoidHom).map e.toMonoidHom : Subgroup G) : Set G) := by
        exact map_centralizer_eq_of_equiv (e := e) (P := P.map e.symm.toMonoidHom)
      _ = C := by
        rw [hP0_map]
  have hcomp₁ : eTot.toMonoidHom = e.toMonoidHom.comp eT.toMonoidHom := by
    dsimp [eTot]
  have heTot : (C0.subgroupOf (⊤ : Subgroup T)).map eTot.toMonoidHom = C := by
    rw [hcomp₁, ← Subgroup.map_map, he_subgroupOf, he_centralizer]
  let Φ₁ : ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T) ≃* G ⧸ C :=
    QuotientGroup.congr (G := ↥(⊤ : Subgroup T)) (H := G)
      (G' := C0.subgroupOf (⊤ : Subgroup T)) (H' := C) eTot heTot
  have hcore₁ : (pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T))).map Φ₁.toMonoidHom =
      pCore p (G ⧸ C) :=
    pCore_map_iso (G := ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) (G' := G ⧸ C)
      (p := p) (f := Φ₁)
  have hmem₁ : Φ₁ (QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩) ∈ pCore p (G ⧸ C) := by
    rw [← hcore₁]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩, hconcl1, rfl⟩
  have happly₁ : Φ₁ (QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩) = QuotientGroup.mk' C x := by
    dsimp [Φ₁]
    rfl
  have hconcl : QuotientGroup.mk' C x ∈ pCore p (G ⧸ C) := by
    rw [happly₁] at hmem₁
    exact hmem₁
  simpa [C] using hconcl

end CFSG.Glauberman
