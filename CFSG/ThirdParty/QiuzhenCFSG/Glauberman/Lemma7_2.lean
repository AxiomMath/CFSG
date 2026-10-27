module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.pStability
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — Lemma 7.2

This file proves Lemma 7.2 of [6] (Glauberman, *A Characteristic Subgroup of a p-Stable
Group*, Canad. J. Math. 20 (1968), 1101–1135), following the validated transcription in
`refs/glauberman-p-stable.tex` L1840–L1872:

> **Lemma.** Let `p` be an odd prime and let `G` be a finite `p`-stable group such that
> `O_p(G) ≠ 1`.  Then `G / O_{p'}(G)` is `p`-stable.

Formal statements:
* `lemma7_2_local` — the Definition-2.1-level conclusion for the quotient `G ⧸ M₀`
  (`M₀ = pPrimeCore p G`): `pStableLocal p (G ⧸ M₀)`.  This is what the paper actually
  proves: let `P̄ ⊴ Ḡ` be a normal `p`-subgroup of `Ḡ = G/M₀` and `x̄ ∈ Ḡ` with
  `[P̄, x̄, x̄] = 1`; pulling `P̄` back to `P ⊴ G` (`M₀ ⊆ P`, `P/M₀ = P̄`), choosing a
  Sylow `p`-subgroup `P₀` of `P`, applying the Frattini argument (`G = M₀·N(P₀)`) to
  represent `x̄` by `x ∈ N(P₀)`, and using `p`-stability of `G` (via
  `pStableLocal_of_core_ne_bot`), one obtains `x̄ ∈ O_p(N_{Ḡ}(P̄)/C_{Ḡ}(P̄))`.
* `lemma7_2` — the paper's conclusion `pStable p (G ⧸ M₀)` in the Definition-2.3 sense:
  since `O_p(Ḡ) ≠ 1` (Lemma `pCore_quotient_ne_bot_of_ne_bot`), the maximal set
  `M_p(Ḡ)` is the singleton `{⊤}` (`MpSet_eq_top_of_core_ne_bot`), so
  `pStable p Ḡ` reduces to `pStableLocal p Ḡ`, transported to `↥M̄` for the unique
  `M̄ ∈ M_p(Ḡ)` along the isomorphism `↥M̄ ≃* Ḡ` (`pStableLocal_congr`).

The paper's argument is the `p`-stability-of-quotient input for the verification of
condition `(F_p)` in Theorem C.

Supporting infrastructure proved here (all without `axiom`/`opaque`/`sorry`):
* `pStableLocal_congr` — `pStableLocal` is invariant under group isomorphism; this is the
  transport that connects the wrapper's `pStable` (quantifying over `M ∈ M_p(G)`) with the
  group-level `pStableLocal` condition.
* `pStableLocal_of_core_ne_bot` — `pStable p G` + `O_p(G) ≠ 1` ⟹ `pStableLocal p G`
  (`⊤ ∈ M_p(G)` since `O_p(⊤) = O_p(G) ≠ 1`).
* `mem_MpSet_top` / `MpSet_eq_top_of_core_ne_bot` — the singleton lemma
  `M_p(G) = {⊤}` when `O_p(G) ≠ 1`.
* `pCore_quotient_ne_bot_of_ne_bot` — `O_p(G) ≠ 1` ⟹ `O_p(G/O_{p'}(G)) ≠ 1`
  (paper: "`O_p(overline G) ≠ 1`").
* local copies of non-exported infrastructure (`normalizer_le_normalizer_centralizer`,
  `pCore_map_le_pCore_of_surjective`, `quotient_pPrimeCore_subgroupMap_injective`).

The commutator convention note of the round-1 modules applies: `⁅⁅P, Subgroup.zpowers x⁆,
Subgroup.zpowers x⁆ = ⊥` is the formal transcription of the paper's `[P,x,x] = 1`, and the
element-identity differences between the paper's left convention and Mathlib's right
convention are immaterial at the subgroup level.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-! ## Local copies of non-exported infrastructure -/

/-- The normalizer of a subgroup normalizes its centralizer: `N_G(R) ≤ N_G(C_G(R))`.
(Re-derivation of the non-exported `normalizer_le_normalizer_centralizer` from
`FeitThompson/PCore/CentralizerControl.lean`.) -/
private lemma normalizer_le_normalizer_centralizer (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have hrn : n⁻¹ * r * n ∈ R := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hn) _).1 hr
    have hcomm : (n⁻¹ * r * n) * c = c * (n⁻¹ * r * n) := hc _ hrn
    have hcomm' := congrArg (fun x : G => n * x * n⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have hrn : n * r * n⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hn _).1 hr
    have hcomm :
        (n * r * n⁻¹) * (n * c * n⁻¹) = (n * c * n⁻¹) * (n * r * n⁻¹) :=
      hc _ hrn
    have hcomm' := congrArg (fun x : G => n⁻¹ * x * n) hcomm
    simpa [mul_assoc] using hcomm'

/-- The image of `O_p(G)` under a surjective homomorphism is contained in `O_p(H)`.
(Re-derivation of the non-exported `pCore_map_le_pCore_of_surjective` from
`FeitThompson/Gorenstein/Chapter8_2.lean`.) -/
private theorem pCore_map_le_pCore_of_surjective {H : Type*} [Group H] [Finite G]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f) :
    (pCore p G).map f ≤ pCore p H := by
  exact le_sSup <|
    And.intro
      (Subgroup.Normal.map (H := pCore p G) inferInstance f hf)
      (IsPGroup.map (p := p) (H := pCore p G) (pCore_isPGroup (G := G) (p := p)) f)

/-- Restriction of the quotient map `G → G/O_{p'}(G)` to a `p`-subgroup `H` is injective.
(Re-derivation of the non-exported `quotient_pPrimeCore_subgroupMap_injective` from
`FeitThompson/Gorenstein/Chapter8_2.lean`.) -/
private theorem quotient_pPrimeCore_subgroupMap_injective [Finite G] (p : ℕ)
    [Fact p.Prime] (H : Subgroup G) (hHp : IsPGroup p H) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore p G)).comp H.subtype) := by
  let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
  have hcoprime : Nat.Coprime (Nat.card H) (Nat.card (pPrimeCore p G)) := by
    rcases IsPGroup.iff_card.mp hHp with ⟨n, hcard⟩
    rw [hcard]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hinf_bot : H ⊓ pPrimeCore p G = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
  have hker_bot : (((q.comp H.subtype)).ker : Subgroup H) = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxM : ((x : H) : G) ∈ pPrimeCore p G := by
        exact
          (QuotientGroup.eq_one_iff (N := pPrimeCore p G) (x := ((x : H) : G))).1 hx
      have hxbot : ((x : H) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinf_bot]
        exact ⟨x.2, hxM⟩
      simpa using hxbot
    · intro hx
      change q ((x : H) : G) = 1
      have hx1 : x = 1 := by simpa [Subgroup.mem_bot] using hx
      rw [hx1]
      simp [q]
  exact (MonoidHom.ker_eq_bot_iff (q.comp H.subtype)).1 hker_bot

/-! ## `pStableLocal` is invariant under group isomorphism -/

set_option backward.isDefEq.respectTransparency false in
/-- One direction of `pStableLocal_congr`: `pStableLocal` transports along an isomorphism.
Given `P' ≤ G'`, work with `P = P'.comap e ≤ G`; the hypothesis `(O_{p'}(G') ⊔ P').Normal`
becomes `(O_{p'}(G) ⊔ P).Normal` by transport along `e` (the `p'`-core and the normalizer
and centralizer all commute with the isomorphism), and the conclusion is transported back
via `QuotientGroup.congr` and `pCore_map_iso`. -/
private theorem pStableLocal_congr_forward {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    [Fact p.Prime] (e : G ≃* G') (h : pStableLocal p G) : pStableLocal p G' := by
  classical
  intro P' hP'p hnorm' x' hx'N' hcomm'
  let P : Subgroup G := P'.comap e.toMonoidHom
  have hPp : IsPGroup p P :=
    IsPGroup.comap_of_injective (hH := hP'p) (ϕ := e.toMonoidHom) (hϕ := e.injective)
  have hPmap : P.map e.toMonoidHom = P' := by
    dsimp [P]
    exact Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective P'
  have hnorm : (pPrimeCore p G ⊔ P).Normal := by
    have hcomap : (pPrimeCore p G ⊔ P) = ((pPrimeCore p G' ⊔ P').comap e.toMonoidHom) := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective
        (pPrimeCore p G' ⊔ P')]
      rw [Subgroup.map_sup, pPrimeCore_map_iso, hPmap]
    rw [hcomap]
    exact Subgroup.Normal.comap hnorm' e.toMonoidHom
  let x : G := e.symm x'
  have hxN : x ∈ Subgroup.normalizer (P : Set G) := by
    have hnorm_map : (Subgroup.normalizer (P : Set G)).map e.toMonoidHom =
        Subgroup.normalizer (P' : Set G') := by
      rw [Subgroup.map_equiv_normalizer_eq, hPmap]
    have hmem : e x ∈ (Subgroup.normalizer (P : Set G)).map e.toMonoidHom := by
      rw [hnorm_map]
      simpa [x] using hx'N'
    rcases Subgroup.mem_map.mp hmem with ⟨y, hy, hye⟩
    have hyx : y = x := e.injective hye
    simpa [hyx] using hy
  have hcomm : ⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hPmap]
    have hzx : (Subgroup.zpowers x).map e.toMonoidHom = Subgroup.zpowers x' := by
      rw [MonoidHom.map_zpowers]
      congr 1
      simp [x]
    rw [hzx]
    simpa using hcomm'
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have : (C.subgroupOf N).Normal := by
    have hCN : C ≤ N := by simpa [C, N] using (centralizer_le_normalizer (G := G) P)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := C) (K := N) hCN).2
      (normalizer_le_normalizer_centralizer (G := G) P)
  have hconcl : QuotientGroup.mk' (C.subgroupOf N) ⟨x, hxN⟩ ∈
      pCore p (N ⧸ C.subgroupOf N) :=
    h P hPp hnorm x hxN hcomm
  let N' : Subgroup G' := Subgroup.normalizer (P' : Set G')
  let C' : Subgroup G' := Subgroup.centralizer (P' : Set G')
  have : (C'.subgroupOf N').Normal := by
    have hC'N' : C' ≤ N' := by simpa [C', N'] using (centralizer_le_normalizer (G := G') P')
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := C') (K := N') hC'N').2
      (normalizer_le_normalizer_centralizer (G := G') P')
  have hNmap : N.map e.toMonoidHom = N' := by
    rw [Subgroup.map_equiv_normalizer_eq, hPmap]
  have hCmap : C.map e.toMonoidHom = C' := by
    calc
      C.map e.toMonoidHom =
          Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup G') : Set G') :=
        map_centralizer_eq_of_equiv (e := e) (P := P)
      _ = C' := by rw [hPmap]
  let eN : ↥N ≃* ↥N' :=
    { toFun := fun y => ⟨e y.1, by
        have hmem : e y.1 ∈ N.map e.toMonoidHom :=
          Subgroup.mem_map_of_mem e.toMonoidHom y.2
        rwa [hNmap] at hmem⟩
      invFun := fun z => ⟨e.symm z.1, by
        have hNcomap : N'.comap e.toMonoidHom = N := by
          apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
          rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N']
          exact hNmap.symm
        have hm : e.symm z.1 ∈ N'.comap e.toMonoidHom := by
          change e (e.symm z.1) ∈ N'
          simp
        rwa [hNcomap] at hm⟩
      left_inv := fun y => by
        apply Subtype.ext
        change e.symm (e y.1) = (y : G)
        simp
      right_inv := fun z => by
        apply Subtype.ext
        change e (e.symm z.1) = (z : G')
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        change e (a.1 * b.1) = e a.1 * e b.1
        exact e.map_mul a.1 b.1 }
  have he_subgroupOf : (C.subgroupOf N).map eN.toMonoidHom = C'.subgroupOf N' := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by
        have hzC : (z : G) ∈ C := Subgroup.mem_subgroupOf.mp hz
        have hmem : e (z : G) ∈ C.map e.toMonoidHom :=
          Subgroup.mem_map_of_mem e.toMonoidHom hzC
        rwa [hCmap] at hmem)
    · intro hy
      have hyC' : (y : G') ∈ C' := Subgroup.mem_subgroupOf.mp hy
      have hCcomap : C'.comap e.toMonoidHom = C := by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective C']
        exact hCmap.symm
      have hzC : e.symm (y : G') ∈ C := by
        rw [← hCcomap]
        change e (e.symm (y : G')) ∈ C'
        simpa using hyC'
      have hzN : e.symm (y : G') ∈ N := by
        have hNcomap : N'.comap e.toMonoidHom = N := by
          apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
          rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N']
          exact hNmap.symm
        rw [← hNcomap]
        change e (e.symm (y : G')) ∈ N'
        simp
      refine ⟨⟨e.symm (y : G'), hzN⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hzC
      · apply Subtype.ext
        change e (e.symm (y : G')) = (y : G')
        simp
  let Φ : ↥N ⧸ C.subgroupOf N ≃* ↥N' ⧸ C'.subgroupOf N' :=
    QuotientGroup.congr (G := ↥N) (H := ↥N')
      (G' := C.subgroupOf N) (H' := C'.subgroupOf N') eN he_subgroupOf
  have hcore : (pCore p (↥N ⧸ C.subgroupOf N)).map Φ.toMonoidHom =
      pCore p (↥N' ⧸ C'.subgroupOf N') :=
    pCore_map_iso (G := ↥N ⧸ C.subgroupOf N) (G' := ↥N' ⧸ C'.subgroupOf N')
      (p := p) (f := Φ)
  have hmem' : Φ (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hxN⟩) ∈
      pCore p (↥N' ⧸ C'.subgroupOf N') := by
    rw [← hcore]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C.subgroupOf N) ⟨x, hxN⟩, hconcl, rfl⟩
  have happly : Φ (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hxN⟩) =
      QuotientGroup.mk' (C'.subgroupOf N') ⟨x', hx'N'⟩ := by
    dsimp [Φ]
    change QuotientGroup.mk' (C'.subgroupOf N') (eN ⟨x, hxN⟩) =
      QuotientGroup.mk' (C'.subgroupOf N') ⟨x', hx'N'⟩
    congr 1
    apply Subtype.ext
    change e (x : G) = (x' : G')
    simp [x]
  have hconcl' : QuotientGroup.mk' (C'.subgroupOf N') ⟨x', hx'N'⟩ ∈
      pCore p (↥N' ⧸ C'.subgroupOf N') := by
    rw [happly] at hmem'
    exact hmem'
  simpa [N', C'] using hconcl'

/-- `pStableLocal` is invariant under group isomorphism: for `e : G ≃* G'` one has
`pStableLocal p G ↔ pStableLocal p G'`.  Used to move the `pStableLocal` conclusion between
a group and its isomorphic copy `↥(⊤ : Subgroup G)`, and to apply the `pStable` hypothesis
(`M ∈ M_p(G)`) to the whole group. -/
public theorem pStableLocal_congr {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    [Fact p.Prime] (e : G ≃* G') : pStableLocal p G ↔ pStableLocal p G' := by
  constructor
  · exact pStableLocal_congr_forward p e
  · exact pStableLocal_congr_forward p e.symm

/-! ## From `pStable` to `pStableLocal` when `O_p(G) ≠ 1` -/

/-- `⊤ ≤ G` lies in `M_p(G)` when `O_p(G) ≠ 1`: `O_p(⊤) = O_p(G) ≠ ⊥` via the canonical
isomorphism `⊤ ≃ G`, and maximality is trivial. -/
public theorem mem_MpSet_top (p : ℕ) [Fact p.Prime] (hOp : pCore p G ≠ ⊥) :
    (⊤ : Subgroup G) ∈ MpSet p G := by
  change pCore p (↥(⊤ : Subgroup G)) ≠ ⊥ ∧
    ∀ K : Subgroup G, pCore p (↥K) ≠ ⊥ → (⊤ : Subgroup G) ≤ K → K = (⊤ : Subgroup G)
  constructor
  · intro hbot
    apply hOp
    have hmap := pCore_map_iso (G := ↥(⊤ : Subgroup G)) (G' := G) (p := p)
      (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G))
    simpa [hbot] using hmap.symm
  · intro K hKne htople
    exact le_antisymm le_top htople

/-- When `O_p(G) ≠ 1`, the set `M_p(G)` is the singleton `{⊤}`: every maximal subgroup
with `O_p ≠ 1` is all of `G` (because `⊤` itself has `O_p(⊤) = O_p(G) ≠ 1`). -/
public theorem MpSet_eq_top_of_core_ne_bot (p : ℕ) [Fact p.Prime]
    (hOp : pCore p G ≠ ⊥) : ∀ M : Subgroup G, M ∈ MpSet p G → M = ⊤ := by
  intro M hM
  exact (hM.2 (⊤ : Subgroup G) (mem_MpSet_top (G := G) p hOp).1 le_top).symm

/-- The Theorem-A application shape of the `pStable` hypothesis: when `O_p(G) ≠ 1`, the
whole group `G` is `p`-stable in the sense of Definition 2.1.  This is
`pStable p G` instantiated at `M = ⊤ ∈ M_p(G)` and transported from `↥⊤` to `G` along the
canonical isomorphism (Lemma `pStableLocal_congr`). -/
public theorem pStableLocal_of_core_ne_bot (p : ℕ) [Fact p.Prime]
    (hstab : pStable p G) (hOp : pCore p G ≠ ⊥) : pStableLocal p G := by
  have htop : pStableLocal p (↥(⊤ : Subgroup G)) :=
    hstab (⊤ : Subgroup G) (mem_MpSet_top (G := G) p hOp)
  exact (pStableLocal_congr (p := p)
    (e := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G))).1 htop

/-! ## `O_p` of the quotient by the `p'`-core -/

/-- `O_p(G/O_{p'}(G)) ≠ 1` whenever `O_p(G) ≠ 1`: the image of `O_p(G)` in the quotient is
a non-trivial normal `p`-subgroup (it is non-trivial because `O_p(G) ∩ O_{p'}(G) = 1` by
coprimality).  This is the paper's "`O_p(overline G) ≠ 1`" ([6], Lemma 7.2, proof,
`refs/glauberman-p-stable.tex` L1844). -/
private theorem pCore_quotient_ne_bot_of_ne_bot [Finite G] (p : ℕ) [Fact p.Prime]
    (hOp : pCore p G ≠ ⊥) : pCore p (G ⧸ pPrimeCore p G) ≠ ⊥ := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hmap_ne : (pCore p G).map q ≠ ⊥ := by
    intro hmap_bot
    have hleM : pCore p G ≤ M := by
      simpa [q, M, QuotientGroup.ker_mk'] using
        (Subgroup.map_eq_bot_iff (f := q) (H := pCore p G)).1 hmap_bot
    have hcopM : Nat.Coprime p (Nat.card M) := by
      simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
    rcases (IsPGroup.iff_card.mp (pCore_isPGroup (G := G) (p := p))) with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card (pCore p G)) (Nat.card M) := by
      rw [hn]
      exact hcopM.pow_left n
    have hinf : pCore p G ⊓ M = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    have hEq : pCore p G = ⊥ := by
      rw [inf_eq_left.mpr hleM] at hinf
      exact hinf
    exact hOp hEq
  have hle : (pCore p G).map q ≤ pCore p (G ⧸ M) :=
    pCore_map_le_pCore_of_surjective (G := G) (H := G ⧸ M) (p := p) q
      (QuotientGroup.mk'_surjective M)
  intro hbot
  exact hmap_ne (by
    apply le_antisymm _ bot_le
    intro y hy
    have hy' : y ∈ pCore p (G ⧸ M) := hle hy
    rw [hbot] at hy'
    exact hy')

/-! ## Lemma 7.2 (main statements) -/

/-- **Lemma 7.2, local form** ([6], Lemma 7.2, proof; `refs/glauberman-p-stable.tex`
L1840–L1872): if `p` is an odd prime, `G` is finite, `p`-stable, and `O_p(G) ≠ 1`, then
`G/O_{p'}(G)` satisfies the Definition-2.1 condition — for every `p`-subgroup `P̄` of
`Ḡ = G/O_{p'}(G)` with `O_{p'}(Ḡ)P̄ ⊴ Ḡ` (i.e. `P̄ ⊴ Ḡ`, since
`O_{p'}(Ḡ) = 1`) and every `x̄ ∈ N_{Ḡ}(P̄)` with `[P̄,x̄,x̄] = 1`, the coset of
`C_{Ḡ}(P̄)` in `N_{Ḡ}(P̄)` lies in `O_p(N_{Ḡ}(P̄)/C_{Ḡ}(P̄))`.

The proof follows the paper: pull `P̄` back to `P ⊴ G` with `O_{p'}(G) ⊆ P` and
`P/O_{p'}(G) = P̄`; take `P₀` a Sylow `p`-subgroup of `P` (`P₀` maps onto `P̄` since
`P̄` is a `p`-group and `P/O_{p'}(G) = P̄`); by the Frattini argument
(`G = O_{p'}(G)·N_G(P₀)`) choose `x ∈ N_G(P₀)` in the coset `x̄`; the commutator
`[P̄,x̄,x̄] = 1` lifts to `[P,x,x] ⊆ O_{p'}(G)`, hence `[P₀,x,x] ⊆ P₀ ∩ O_{p'}(G) = 1`;
`p`-stability of `G` (`pStableLocal_of_core_ne_bot`) gives the coset of `C_G(P₀)` in
`O_p(N_G(P₀)/C_G(P₀))`; the quotient-centralizer identities
(`centralizer_map_quotient_eq_map_centralizer`,
`normalizer_map_quotient_eq_map_normalizer`) transport this to
`x̄ ∈ O_p(N_{Ḡ}(P̄)/C_{Ḡ}(P̄))` along the surjective map
`N_G(P₀)/C_G(P₀) → N_{Ḡ}(P̄)/C_{Ḡ}(P̄)`, using
`pCore_map_le_pCore_of_surjective`. -/
public theorem lemma7_2_local {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (_hpodd : p ≠ 2) (hstab : pStable p G) (hOp : pCore p G ≠ ⊥) :
    pStableLocal p (G ⧸ pPrimeCore p G) := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hM_normal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hM_normal
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hquot_core_bot : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hstabLocal : pStableLocal p G := pStableLocal_of_core_ne_bot (G := G) p hstab hOp
  intro Pbar hPbarp hnorm' xbar hxbarN hcomm'
  have hPbar_normal : Pbar.Normal := by
    rw [hquot_core_bot, bot_sup_eq] at hnorm'
    exact hnorm'
  let P : Subgroup G := Pbar.comap q
  have hP_normal : P.Normal := hPbar_normal.comap q
  have : P.Normal := hP_normal
  have hPmap : P.map q = Pbar :=
    Subgroup.map_comap_eq_self_of_surjective (f := q) hqsurj Pbar
  have hM_le_P : M ≤ P := by
    intro m hm
    change q m ∈ Pbar
    have hq1 : q m = 1 := (QuotientGroup.eq_one_iff (N := M) (x := m)).2 hm
    simp [hq1]
  let P0 : Sylow p (↥P) := Classical.choice (Sylow.nonempty (p := p) (G := ↥P))
  have : Finite (Sylow p (↥P)) := Sylow.finite_of_finiteIndex P0
  let P0G : Subgroup G := (P0 : Subgroup (↥P)).map P.subtype
  have hP0p : IsPGroup p P0G := by
    simpa [P0G] using
      IsPGroup.map (p := p) (H := (P0 : Subgroup (↥P))) P0.isPGroup' P.subtype
  have hP0_le_P : P0G ≤ P := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  -- `P₀` maps onto `P̄` (a Sylow `p`-subgroup of `P` maps onto the `p`-group `P/M = P̄`)
  let qQ : ↥P →* ↥Pbar :=
    (q.comp P.subtype).codRestrict Pbar (by
      intro x
      exact x.2)
  have hqQ_surj : Function.Surjective qQ := by
    intro x
    rcases QuotientGroup.mk'_surjective M x.1 with ⟨y, hy⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change q y ∈ Pbar
      rw [hy]
      exact x.2
    · apply Subtype.ext
      change q y = (x : G ⧸ M)
      exact hy
  have hP0_map_top :
      ((P0.mapSurjective (f := qQ) hqQ_surj : Sylow p (↥Pbar)) : Subgroup (↥Pbar)) = ⊤ := by
    apply le_antisymm le_top
    exact ((P0.mapSurjective (f := qQ) hqQ_surj).is_maximal'
      (hPbarp.to_subgroup (⊤ : Subgroup (↥Pbar))) le_top).le
  have hP0G_map_q : P0G.map q = Pbar := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      change q y ∈ Pbar
      have hymap : q y ∈ P.map q := Subgroup.mem_map_of_mem q (hP0_le_P hy)
      rwa [hPmap] at hymap
    · intro x hx
      have hxS : (⟨x, hx⟩ : ↥Pbar) ∈
          ((P0.mapSurjective (f := qQ) hqQ_surj : Sylow p (↥Pbar)) : Subgroup (↥Pbar)) := by
        rw [hP0_map_top]
        simp
      rw [Sylow.coe_mapSurjective] at hxS
      rcases Subgroup.mem_map.mp hxS with ⟨z, hz, hzx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨z.1, Subgroup.mem_map_of_mem P.subtype hz, ?_⟩
      exact congrArg Subtype.val hzx
  -- `P = M·P₀`, so `M·P₀ ⊴ G` (hypothesis of Definition 2.1 for the `p`-subgroup `P₀`)
  have hM_sup_P0G : M ⊔ P0G = P := by
    apply le_antisymm
    · exact sup_le hM_le_P hP0_le_P
    · calc
        P ≤ (P0G.map q).comap q := by
          rw [hP0G_map_q]
        _ ≤ M ⊔ P0G := by
          exact le_of_eq (by
            simp [q])
  have hMQ0_normal : (M ⊔ P0G).Normal := by
    rw [hM_sup_P0G]
    exact hP_normal
  -- Frattini argument: `G = M·N_G(P₀)`
  have hFrattini : M ⊔ Subgroup.normalizer (P0G : Set G) = ⊤ := by
    have hF : Subgroup.normalizer (P0G : Set G) ⊔ P = ⊤ := by
      simpa [P0G] using (Sylow.normalizer_sup_eq_top (N := P) P0)
    apply le_antisymm le_top
    rw [← hF]
    refine sup_le ?_ ?_
    · exact le_sup_right
    · rw [← hM_sup_P0G]
      exact sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right)
  -- choose `x ∈ N(P₀)` in the coset `x̄`
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective M xbar
  have hgFrattini : g ∈ M ⊔ Subgroup.normalizer (P0G : Set G) := by
    rw [hFrattini]
    trivial
  rcases (Subgroup.mem_sup_of_normal_left (s := M)
    (t := Subgroup.normalizer (P0G : Set G))).1 hgFrattini with ⟨m, hmM, x, hxN, hmx⟩
  have hqx : q x = xbar := by
    have hqmx : q (m * x) = q x := by
      have hqm : q m = 1 := (QuotientGroup.eq_one_iff (N := M) (x := m)).2 hmM
      simp [hqm]
    rw [← hmx, hqmx] at hg
    exact hg
  -- lift `[P̄,x̄,x̄] = 1` to `[P,x,x] ⊆ M`
  have hcommP_le_M : ⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ≤ M := by
    intro y hy
    have hymap : q y ∈ (⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆).map q :=
      Subgroup.mem_map_of_mem q hy
    have hmap_bot : (⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆).map q = ⊥ := by
      calc
        (⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆).map q
            = ⁅⁅P.map q, (Subgroup.zpowers x).map q⁆, (Subgroup.zpowers x).map q⁆ := by
                rw [Subgroup.map_commutator, Subgroup.map_commutator]
        _ = ⁅⁅Pbar, Subgroup.zpowers xbar⁆, Subgroup.zpowers xbar⁆ := by
                rw [hPmap, MonoidHom.map_zpowers, hqx]
        _ = ⊥ := hcomm'
    have hy1 : q y = 1 := by
      have hybot : q y ∈ (⊥ : Subgroup (G ⧸ M)) := by simpa [hmap_bot] using hymap
      simpa using hybot
    exact (QuotientGroup.eq_one_iff (N := M) (x := y)).1 hy1
  -- `[P₀,x,x] ⊆ P₀` (since `x ∈ N(P₀)`)
  have hcommP0_le_P0 : ⁅⁅P0G, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ≤ P0G := by
    have hzx_le : Subgroup.zpowers x ≤ Subgroup.normalizer (P0G : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have hc1 : ⁅Subgroup.zpowers x, P0G⁆ ≤ P0G :=
      (Subgroup.le_normalizer_iff_commutator_le_right).1 hzx_le
    have hc1' : ⁅P0G, Subgroup.zpowers x⁆ ≤ P0G := by
      simpa [Subgroup.commutator_comm] using hc1
    exact (Subgroup.commutator_mono hc1' le_rfl).trans hc1'
  -- `P₀ ∩ M = 1` (coprimality of orders)
  have hP0_inf_M : P0G ⊓ M = ⊥ := by
    rcases (IsPGroup.iff_card.mp hP0p) with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card (↥P0G)) (Nat.card M) := by
      rw [hn]
      exact hMcop.pow_left n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hcomm0 : ⁅⁅P0G, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    have hyP0 : y ∈ P0G := hcommP0_le_P0 hy
    have hyM : y ∈ M := hcommP_le_M
      (Subgroup.commutator_mono (Subgroup.commutator_mono hP0_le_P le_rfl) le_rfl hy)
    have hybot : y ∈ (⊥ : Subgroup G) := by
      rw [← hP0_inf_M]
      exact ⟨hyP0, hyM⟩
    exact hybot
  -- Definition 2.1 for `G` applied to the `p`-subgroup `P₀` and `x ∈ N(P₀)`
  let N0 : Subgroup G := Subgroup.normalizer (P0G : Set G)
  let C0 : Subgroup G := Subgroup.centralizer (P0G : Set G)
  have : (C0.subgroupOf N0).Normal := by
    have hC0N0 : C0 ≤ N0 := by simpa [C0, N0] using (centralizer_le_normalizer (G := G) P0G)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := C0) (K := N0) hC0N0).2
      (normalizer_le_normalizer_centralizer (G := G) P0G)
  have hconcl0 : QuotientGroup.mk' (C0.subgroupOf N0) ⟨x, hxN⟩ ∈
      pCore p (N0 ⧸ C0.subgroupOf N0) :=
    hstabLocal P0G hP0p hMQ0_normal x hxN hcomm0
  -- transport to the quotient `Ḡ = G/M`
  let Nbar : Subgroup (G ⧸ M) := Subgroup.normalizer (Pbar : Set (G ⧸ M))
  let Cbar : Subgroup (G ⧸ M) := Subgroup.centralizer (Pbar : Set (G ⧸ M))
  have : (Cbar.subgroupOf Nbar).Normal := by
    have hCbarNbar : Cbar ≤ Nbar := by
      simpa [Cbar, Nbar] using (centralizer_le_normalizer (G := G ⧸ M) Pbar)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := Cbar) (K := Nbar) hCbarNbar).2
      (normalizer_le_normalizer_centralizer (G := G ⧸ M) Pbar)
  have himage :
      ((fun a : G => q a) '' (P0G : Set G)) = ((P0G.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_map_of_mem q hy
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hNmap : N0.map q = Nbar := by
    let : Fact (IsPGroup p (↥P0G)) := ⟨hP0p⟩
    have htmp := normalizer_map_quotient_eq_map_normalizer (G := G) (p := p) P0G M hM_normal hMcop
    change Subgroup.normalizer ((fun a : G => q a) '' (P0G : Set G)) = N0.map q at htmp
    have htmp' : Subgroup.normalizer ((P0G.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) = N0.map q := by
      rw [← himage]
      exact htmp
    simpa [Nbar, hP0G_map_q] using htmp'.symm
  have hCmap : C0.map q = Cbar := by
    let : Fact (IsPGroup p (↥P0G)) := ⟨hP0p⟩
    have htmp := centralizer_map_quotient_eq_map_centralizer (G := G) (p := p) (T := P0G)
      (M := M) hM_normal hMcop
    change Subgroup.centralizer ((fun a : G => q a) '' (P0G : Set G)) = C0.map q at htmp
    have htmp' : Subgroup.centralizer ((P0G.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) = C0.map q := by
      rw [← himage]
      exact htmp
    simpa [Cbar, hP0G_map_q] using htmp'.symm
  let qN0 : N0 →* Nbar :=
    (q.comp N0.subtype).codRestrict Nbar (by
      intro x
      have hxmap : q x ∈ N0.map q := Subgroup.mem_map_of_mem q x.2
      rwa [hNmap] at hxmap)
  have hqN0_surj : Function.Surjective qN0 := by
    intro y
    have hy : (y : G ⧸ M) ∈ N0.map q := by
      simpa [← hNmap] using y.2
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change q x = (y : G ⧸ M)
    exact hxy
  have hC0_le_comap : C0.subgroupOf N0 ≤ (Cbar.subgroupOf Nbar).comap qN0 := by
    intro x hx
    change q ((x : N0) : G) ∈ Cbar
    have hxmap : q ((x : N0) : G) ∈ C0.map q :=
      Subgroup.mem_map.mpr ⟨((x : N0) : G), (Subgroup.mem_subgroupOf.mp hx), rfl⟩
    rwa [hCmap] at hxmap
  let phi : N0 ⧸ C0.subgroupOf N0 →* Nbar ⧸ Cbar.subgroupOf Nbar :=
    QuotientGroup.map (N := C0.subgroupOf N0) (M := Cbar.subgroupOf Nbar) qN0 hC0_le_comap
  have hphi_surj : Function.Surjective phi := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro z
    rcases hqN0_surj z with ⟨x, rfl⟩
    refine ⟨QuotientGroup.mk' (C0.subgroupOf N0) x, ?_⟩
    simp [phi]
  have hmap_le : (pCore p (N0 ⧸ C0.subgroupOf N0)).map phi ≤
      pCore p (Nbar ⧸ Cbar.subgroupOf Nbar) :=
    pCore_map_le_pCore_of_surjective (G := N0 ⧸ C0.subgroupOf N0)
      (H := Nbar ⧸ Cbar.subgroupOf Nbar) (p := p) phi hphi_surj
  have hmem_target : QuotientGroup.mk' (Cbar.subgroupOf Nbar) ⟨xbar, hxbarN⟩ ∈
      pCore p (Nbar ⧸ Cbar.subgroupOf Nbar) := by
    have hphi_x : phi (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x, hxN⟩) =
        QuotientGroup.mk' (Cbar.subgroupOf Nbar) ⟨xbar, hxbarN⟩ := by
      have hphi_x' : phi (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x, hxN⟩) =
          QuotientGroup.mk' (Cbar.subgroupOf Nbar) (qN0 ⟨x, hxN⟩) := by
        simp [phi]
      have hq : qN0 ⟨x, hxN⟩ = ⟨xbar, hxbarN⟩ := by
        apply Subtype.ext
        change q ((⟨x, hxN⟩ : N0) : G) = xbar
        simpa using hqx
      rw [hq] at hphi_x'
      exact hphi_x'
    have hmem_map : phi (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x, hxN⟩) ∈
        (pCore p (N0 ⧸ C0.subgroupOf N0)).map phi :=
      Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C0.subgroupOf N0) ⟨x, hxN⟩, hconcl0, rfl⟩
    rw [hphi_x] at hmem_map
    exact hmap_le hmem_map
  simpa [Nbar, Cbar] using hmem_target

/-- **Lemma 7.2** ([6], §7; `refs/glauberman-p-stable.tex` L1840–L1843): let `p` be an odd
prime and let `G` be a finite `p`-stable group such that `O_p(G) ≠ 1`.  Then
`G/O_{p'}(G)` is `p`-stable.

The quotient `Ḡ = G/O_{p'}(G)` satisfies `O_{p'}(Ḡ) = 1`
(`pPrimeCore_quotient_pPrimeCore_eq_bot`) and `O_p(Ḡ) ≠ 1`
(`pCore_quotient_ne_bot_of_ne_bot`), so `M_p(Ḡ) = {⊤}`
(`MpSet_eq_top_of_core_ne_bot`); hence `pStable p Ḡ` is `pStableLocal p Ḡ`
(`lemma7_2_local`) transported along `↥M̄ ≃* Ḡ` for the unique `M̄ ∈ M_p(Ḡ)`
(`pStableLocal_congr`).  This is the `p`-stability-of-quotient input for Theorem C's
condition `(F_p)`. -/
public theorem lemma7_2 {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (hstab : pStable p G) (hOp : pCore p G ≠ ⊥) :
    pStable p (G ⧸ pPrimeCore p G) := by
  classical
  let Gbar : Type _ := G ⧸ pPrimeCore p G
  have hOp_quot : pCore p Gbar ≠ ⊥ := by
    dsimp [Gbar]
    exact pCore_quotient_ne_bot_of_ne_bot (G := G) p hOp
  have hloc : pStableLocal p Gbar := by
    dsimp [Gbar]
    exact lemma7_2_local (G := G) p hpodd hstab hOp
  intro Mbar hMbar
  have hMbar_top : Mbar = ⊤ := MpSet_eq_top_of_core_ne_bot (G := Gbar) p hOp_quot Mbar hMbar
  have hlocTop : pStableLocal p (↥(⊤ : Subgroup Gbar)) :=
    (pStableLocal_congr (p := p)
      (e := (Subgroup.topEquiv : (⊤ : Subgroup Gbar) ≃* Gbar))).2 hloc
  let e1 : ↥Mbar ≃* ↥(⊤ : Subgroup Gbar) :=
    { toEquiv := Equiv.subtypeEquivRight (fun y : Gbar => by rw [hMbar_top])
      map_mul' := by intro a b; rfl }
  exact (pStableLocal_congr (p := p) (e := e1.symm)).1 hlocTop

end CFSG.Glauberman
