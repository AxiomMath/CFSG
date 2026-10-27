module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# The control-core bridge for Lemma 2.3

This module implements the control-core route decided in the proof review
on the proof review: the paper-to-Lean bridge for `lemma_2_3` is **not** the
containment `F*(A) ≤ B` (false in general: S₄ example), but the relation
`ControlCore A B` of `GorensteinWalter/Defs.lean` — the hypothesis shape of
Bender [1, Satz 1.7], which the frozen [1]-statements
`bender1970_1_7_i_oddCoreDisjoint` and
`bender1970_1_7_iii_equalityOfMaximal` consume verbatim.

Contents:

* Infrastructure: in a finite nilpotent subgroup, every subgroup is
  subnormal (proved from the normalizer condition);
* Infrastructure: joins with a centralizing subgroup preserve subnormality;
* the component--subnormal dichotomy `component_le_or_commutator_eq_bot`
  (KS 6.5.2, strong induction on `Nat.card`), its corollaries
  `component_le_or_commutator_eq_bot_of_normal` and `component_commute_of_ne`
  (KS 6.5.3), and the layer-centralizes-Fitting chain
  `component_centralizes_internal_fitting`,
  `component_centralizes_fittingSubgroupOf`, `layer_centralizes_fitting`;
* the public bridge `controlCore_of_normalizerControlledBy`;
* the arrow alternative `lemma_2_3_of_controlCore` — the [1, 1.6/1.7]
  application that discharges `lemma_2_3` in `Section2/Basic.lean`.

**Route:** the classical core is the
component--subnormal dichotomy of Kurzweil--Stellmacher 6.5.2 — if `K` is
a component of the finite group `G` and `U` is subnormal in `G`, then
`K ≤ U` or `⁅K, U⁆ = ⊥` — proved here by strong induction on `Nat.card`
of the ambient group (`component_le_or_commutator_eq_bot`).  The earlier
reduction tree recorded in the earlier pass (normal-step lemma ⟸ crux
⟸ disjoint sub-claim ⟸ distinct-components-commute) was **circular** and
is retired; the correct source order is: the center/top lemma (proved
below) → KS 6.5.2 (the dichotomy, the only hard theorem) → KS 6.5.3
(`component_commute_of_ne`, one line).  From the dichotomy:

```
component_centralizes_internal_fitting  : ⁅E, fittingSubgroup H⁆ = ⊥
component_centralizes_fittingSubgroupOf : ⁅E, fittingSubgroupOf A⁆ = ⊥
layer_centralizes_fitting               : ⁅componentLayerOf A, fittingSubgroupOf A⁆ = ⊥
```

(rule out `E ≤ F(H)` by nilpotency of `F(H)` and
`not_isNilpotent_of_isQuasisimple`), and the public bridge
`controlCore_of_normalizerControlledBy` discharges `lemma_2_3` through
`lemma_2_3_of_controlCore`.  Infrastructure: conjugation transport of
quasisimplicity/subnormality/components, the center/top lemma
(`isSubnormal_le_center_or_eq_top_of_isQuasisimple` — the fundamental fact
about subnormal subgroups of quasisimple groups), component inheritance to
intermediate subgroups, the `subgroupOf` transport wrappers, and the
finite-cardinality bookkeeping.  Proof state is recorded in
`node_graph/section2/lemma_2_3.md`.
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators
open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## Infra: components (layer-centralizes-Fitting route)

The proof review reduces
`layer_centralizes_fitting` to the component--subnormal dichotomy.  This
section carries the verified infrastructure of that route: conjugation
transport of quasisimplicity, the center/top lemma (the fundamental fact:
subnormal subgroups of a quasisimple group are central or the whole group),
and the finite-cardinality wrapper.
-/

/-- The image of the center under a group isomorphism is the center. -/
private lemma map_center_eq_center_of_mulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, ?_⟩
    · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
    · exact e.apply_symm_apply x

/-- Quasisimplicity is invariant under a group isomorphism. -/
private theorem isQuasisimple_mulEquiv
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsQuasisimple G) :
    IsQuasisimple H := by
  have hNontriv : Nontrivial H := by
    let : Nontrivial G := hG.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect H := by
    let : Group.IsPerfect G := (Group.isPerfect_def).2 hG.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.toEquiv.surjective
  have hSimple : IsSimpleGroup (H ⧸ Subgroup.center H) := by
    have he : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
      map_center_eq_center_of_mulEquiv e
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he)).mp hG.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

/-- A component of the ambient group is subnormal in the ambient group. -/
private theorem isSubnormal_of_isComponentOf_top
    {G : Type u} [Group G] {K : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G)) :
    K.IsSubnormal := by
  have h' : ((K.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
    hK.2.1.map (f := (⊤ : Subgroup G).subtype)
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
  rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : K ≤ (⊤ : Subgroup G))] at h'

/-- Conjugation by an ambient element transports quasisimplicity. -/
private theorem isQuasisimple_conjugateSubgroup {G : Type u} [Group G]
    (E : Subgroup G) (g : G) (hE : IsQuasisimple E) :
    IsQuasisimple (conjugateSubgroup E g) :=
  isQuasisimple_mulEquiv ((MulAut.conj g).subgroupMap E) hE

/-- Conjugation by an ambient element transports subnormality. -/
private theorem isSubnormal_conjugateSubgroup {G : Type u} [Group G]
    (E : Subgroup G) (g : G) (hE : E.IsSubnormal) :
    (conjugateSubgroup E g).IsSubnormal := by
  simpa [conjugateSubgroup] using hE.map (MulAut.conj g).surjective

/-- A conjugate of a component of `G` is again a component of `G`. -/
private theorem isComponentOf_conjugateSubgroup {G : Type u} [Group G]
    {E : Subgroup G} (hE : IsComponentOf E (⊤ : Subgroup G)) (g : G) :
    IsComponentOf (conjugateSubgroup E g) (⊤ : Subgroup G) := by
  refine ⟨?_, ?_, isQuasisimple_conjugateSubgroup E g hE.2.2⟩
  · intro x hx
    trivial
  · -- subnormality: ambient `E` subnormal, transported by conjugation
    have hsnE : E.IsSubnormal := by
      have h' : ((E.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
        hE.2.1.map (f := (⊤ : Subgroup G).subtype)
          (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
      rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : E ≤ (⊤ : Subgroup G))] at h'
    exact (isSubnormal_conjugateSubgroup E g hsnE).subgroupOf

/-- A component of `G` contained in `H` is a component of `H` (KS 6.5.2
ingredient: component inheritance to intermediate subgroups). -/
private theorem isComponentOf_subgroupOf
    {G : Type u} [Group G] {K H : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G))
    (hKH : K ≤ H) :
    IsComponentOf (K.subgroupOf H) (⊤ : Subgroup H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    trivial
  · have hKsn : K.IsSubnormal := isSubnormal_of_isComponentOf_top hK
    -- (K.subgroupOf H).subgroupOf (⊤ : Subgroup H) ≅ (K.subgroupOf H) via the bijective ⊤-subtype map
    have hmap' : ((K.subgroupOf H).subgroupOf (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype = K.subgroupOf H :=
      Subgroup.map_subgroupOf_eq_of_le (le_top : K.subgroupOf H ≤ (⊤ : Subgroup H))
    have hsnmap : (((K.subgroupOf H).subgroupOf (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype).IsSubnormal := by
      rw [hmap']
      exact hKsn.subgroupOf
    -- comap back through the bijective map
    have hsnc : (Subgroup.comap (⊤ : Subgroup H).subtype
        (Subgroup.map (⊤ : Subgroup H).subtype ((K.subgroupOf H).subgroupOf (⊤ : Subgroup H)))).IsSubnormal :=
      Subgroup.IsSubnormal.comap (f := (⊤ : Subgroup H).subtype) hsnmap
    have hc' : Subgroup.comap (⊤ : Subgroup H).subtype
          (Subgroup.map (⊤ : Subgroup H).subtype ((K.subgroupOf H).subgroupOf (⊤ : Subgroup H))) =
        (K.subgroupOf H).subgroupOf (⊤ : Subgroup H) := by
      rw [hmap']
      apply le_antisymm
      · intro x hx
        exact (Subgroup.mem_subgroupOf).mpr ((Subgroup.mem_comap).mp hx)
      · intro x hx
        apply (Subgroup.mem_comap).mpr
        exact (Subgroup.mem_subgroupOf).mp hx
    simpa [hc'] using hsnc
  · exact isQuasisimple_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hK.2.2

/-- Finite-cardinality bookkeeping for `subgroupOf` (Mathlib wrapper). -/
private theorem natCard_subgroupOf_eq {G : Type u} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) : Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv

/-- A normal subgroup of a quasisimple group is central or the whole group. -/
public theorem normal_subgroup_le_center_or_eq_top {Q : Type u} [Group Q]
    (hQ : IsQuasisimple Q) (N : Subgroup Q) (hN : N.Normal) :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  let mk : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  have hNbar_sn : (N.map mk).IsSubnormal :=
    (hN.map mk (QuotientGroup.mk'_surjective (Subgroup.center Q))).isSubnormal
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hQ.2.2 hNbar_sn with hbot | htop
  · left
    rw [Subgroup.map_eq_bot_iff] at hbot
    simpa [mk, QuotientGroup.ker_mk'] using hbot
  · right
    -- N·Z(Q) = Q
    have hNZ : N ⊔ Subgroup.center Q = ⊤ := by
      apply eq_top_iff.mpr
      intro q hq
      have hmkq : mk q ∈ N.map mk := by simp [htop]
      rcases Subgroup.mem_map.mp hmkq with ⟨n, hn, hmn⟩
      have hz : n⁻¹ * q ∈ Subgroup.center Q := by
        have h1 : QuotientGroup.mk' (Subgroup.center Q) (n⁻¹ * q) = 1 := by
          simpa [mk] using (by
            rw [map_mul, map_inv, hmn]
            group : mk (n⁻¹ * q) = 1)
        rw [← QuotientGroup.ker_mk' (N := Subgroup.center Q)]
        exact (MonoidHom.mem_ker (f := QuotientGroup.mk' (Subgroup.center Q))).mpr h1
      simpa [mul_assoc] using
        (Subgroup.mul_mem_sup hn hz : n * (n⁻¹ * q) ∈ N ⊔ Subgroup.center Q)
    -- [Q, Q] ≤ N
    have hQQle : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ ⁅N, N⁆ := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hmkq : mk x ∈ N.map mk := by simp [htop]
      rcases Subgroup.mem_map.mp hmkq with ⟨n₁, hn₁, hmn₁⟩
      have hz₁ : n₁⁻¹ * x ∈ Subgroup.center Q := by
        have h1 : QuotientGroup.mk' (Subgroup.center Q) (n₁⁻¹ * x) = 1 := by
          simpa [mk] using (by
            rw [map_mul, map_inv, hmn₁]
            group : mk (n₁⁻¹ * x) = 1)
        rw [← QuotientGroup.ker_mk' (N := Subgroup.center Q)]
        exact (MonoidHom.mem_ker (f := QuotientGroup.mk' (Subgroup.center Q))).mpr h1
      have hmky : mk y ∈ N.map mk := by simp [htop]
      rcases Subgroup.mem_map.mp hmky with ⟨n₂, hn₂, hmn₂⟩
      have hz₂ : n₂⁻¹ * y ∈ Subgroup.center Q := by
        have h1 : QuotientGroup.mk' (Subgroup.center Q) (n₂⁻¹ * y) = 1 := by
          simpa [mk] using (by
            rw [map_mul, map_inv, hmn₂]
            group : mk (n₂⁻¹ * y) = 1)
        rw [← QuotientGroup.ker_mk' (N := Subgroup.center Q)]
        exact (MonoidHom.mem_ker (f := QuotientGroup.mk' (Subgroup.center Q))).mpr h1
      -- [x, y] = [n₁ z₁, n₂ z₂] = [n₁, n₂]
      have hz₁c : Commute (n₁⁻¹ * x) (n₂ * (n₂⁻¹ * y)) :=
        ((Subgroup.mem_center_iff.mp hz₁) (n₂ * (n₂⁻¹ * y))).symm
      have hz₂c : Commute n₁ (n₂⁻¹ * y) := (Subgroup.mem_center_iff.mp hz₂) n₁
      have hz₁y : Commute (n₁⁻¹ * x) y := ((Subgroup.mem_center_iff.mp hz₁) y).symm
      have hxy : ⁅x, y⁆ = ⁅n₁, n₂⁆ := by
        calc
          ⁅x, y⁆ = ⁅n₁ * (n₁⁻¹ * x), n₂ * (n₂⁻¹ * y)⁆ := by
            rw [← show x = n₁ * (n₁⁻¹ * x) by group,
                ← show y = n₂ * (n₂⁻¹ * y) by group]
          _ = ⁅n₁, n₂ * (n₂⁻¹ * y)⁆ := by
            rw [commutatorElement_mul_left_eq_conj_mul]
            simp [Commute.commutator_eq hz₁y]
          _ = ⁅n₁, n₂⁆ := by
            rw [commutatorElement_mul_right_eq_mul_conj]
            simp [Commute.commutator_eq hz₂c]
      rw [hxy]
      exact Subgroup.commutator_mem_commutator hn₁ hn₂
    have hQperf : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
      change _root_.commutator Q = ⊤
      exact hQ.2.1
    have hNtop : (⊤ : Subgroup Q) ≤ N := by
      rw [← hQperf]
      exact hQQle.trans (Subgroup.commutator_le_right (H₁ := N) (H₂ := N))
    exact le_antisymm le_top hNtop

/-- The fundamental fact about quasisimple groups: every subnormal subgroup
is central or the whole group. -/
public theorem isSubnormal_le_center_or_eq_top_of_isQuasisimple {Q : Type u} [Group Q]
    (hQ : IsQuasisimple Q) (N : Subgroup Q) (hN : N.IsSubnormal) :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  rcases Subgroup.IsSubnormal.lt_normal hN with htop | ⟨K, hKnorm, hNK, hKlt⟩
  · right
    exact htop
  · left
    rcases normal_subgroup_le_center_or_eq_top hQ K hKnorm with hKc | hKtop
    · exact hNK.trans hKc
    · exact False.elim (hKlt.ne hKtop)

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
private theorem natCard_lt_of_lt_top
    {G : Type u} [Group G] [Finite G] {H : Subgroup G}
    (hH : H < (⊤ : Subgroup G)) :
    Nat.card H < Nat.card G := by
  have hle : Nat.card H ≤ Nat.card G := Subgroup.card_le_card_group H
  refine lt_of_le_of_ne hle ?_
  intro hcard
  have htop : H = ⊤ := Subgroup.eq_top_of_card_eq H hcard
  exact hH.ne htop

/-- Transport of subgroup containment through `subgroupOf` (restricted to
subgroups contained in the intermediate subgroup). -/
private theorem subgroupOf_le_subgroupOf_iff_of_le
    {G : Type u} [Group G] {A B H : Subgroup G}
    (hAH : A ≤ H) (_hBH : B ≤ H) :
    A.subgroupOf H ≤ B.subgroupOf H ↔ A ≤ B := by
  constructor
  · intro hle x hx
    -- map through H.subtype
    have hm : (A.subgroupOf H).map H.subtype ≤ (B.subgroupOf H).map H.subtype :=
      Subgroup.map_mono (f := H.subtype) hle
    have hx' : H.subtype ⟨x, hAH hx⟩ ∈ (A.subgroupOf H).map H.subtype := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact ⟨hx, hAH hx⟩
    have hy : H.subtype ⟨x, hAH hx⟩ ∈ (B.subgroupOf H).map H.subtype := hm hx'
    rcases Subgroup.mem_map.mp hy with ⟨y, hyB, hxy⟩
    have hyx : (y : ↥H).1 = x := by
      have hyx' : y = (⟨x, hAH hx⟩ : ↥H) := H.subtype_injective hxy
      simpa using (congrArg (fun z : ↥H => (z : ↥H).1) hyx')
    have hy1 : (y : ↥H).1 ∈ B := (Subgroup.mem_subgroupOf).mp hyB
    simpa [hyx] using hy1
  · intro hle
    exact Subgroup.subgroupOf_mono H hle

/-- Transport of commutator triviality through `subgroupOf` (restricted to
subgroups contained in the intermediate subgroup). -/
private theorem commutator_subgroupOf_eq_bot_iff_of_le
    {G : Type u} [Group G] {A B H : Subgroup G}
    (hAH : A ≤ H) (hBH : B ≤ H) :
    ⁅A.subgroupOf H, B.subgroupOf H⁆ = ⊥ ↔ ⁅A, B⁆ = ⊥ := by
  constructor
  · intro hbot
    -- map through H.subtype
    have hmap : (⁅A.subgroupOf H, B.subgroupOf H⁆).map H.subtype = ⊥ := by
      rw [hbot]
      exact Subgroup.map_bot H.subtype
    have hm : ⁅(A.subgroupOf H).map H.subtype, (B.subgroupOf H).map H.subtype⁆ = ⊥ := by
      rw [← Subgroup.map_commutator (H₁ := A.subgroupOf H) (H₂ := B.subgroupOf H) (f := H.subtype)]
      exact hmap
    have hA : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
    have hB : (B.subgroupOf H).map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
    simpa [hA, hB] using hm
  · intro hbot
    -- reflect ⊥ through the injective map
    have hm : (⁅A.subgroupOf H, B.subgroupOf H⁆).map H.subtype = ⊥ := by
      rw [Subgroup.map_commutator (H₁ := A.subgroupOf H) (H₂ := B.subgroupOf H) (f := H.subtype)]
      rw [Subgroup.map_subgroupOf_eq_of_le hAH, Subgroup.map_subgroupOf_eq_of_le hBH]
      exact hbot
    exact (Subgroup.map_eq_bot_iff_of_injective (H := ⁅A.subgroupOf H, B.subgroupOf H⁆)
      (f := H.subtype) (hf := H.subtype_injective)).mp hm

/-- The component--subnormal dichotomy (KS 6.5.2): if `K` is a component of
the finite group `G` and `U` is subnormal in `G`, then `K ≤ U` or
`⁅K, U⁆ = ⊥`.  Proof by strong induction on `Nat.card` of the ambient group,
following Kurzweil--Stellmacher: the trivial branches `U = ⊤` and `K = ⊤`,
then proper normal overgroups `N ∋ K`, `M ∋ U`, the subgroup
`U₁ := ⁅U, K⁆` in their intersection, the recursive application in
`G₁ := N ⊓ N_G(U₁)`, the Three-Subgroups Lemma, and the recursive
application in `M`. -/
public theorem component_le_or_commutator_eq_bot
    {G : Type u} [Group G] [Finite G]
    {K U : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G))
    (hU : U.IsSubnormal) :
    K ≤ U ∨ ⁅K, U⁆ = ⊥ := by
  let P : ℕ → Prop := fun n =>
    ∀ (H : Type u) [Group H] [Finite H], Nat.card H = n →
      ∀ {K U : Subgroup H},
        IsComponentOf K (⊤ : Subgroup H) →
        U.IsSubnormal →
        K ≤ U ∨ ⁅K, U⁆ = ⊥
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih H _ _ hcard K U hK hU
    -- F1: U = ⊤
    by_cases hUtop : U = ⊤
    · left
      rw [hUtop]
      exact le_top
    -- F2: K = ⊤
    by_cases hKtop : K = ⊤
    · have hQ : IsQuasisimple H := by
        rw [hKtop] at hK
        exact isQuasisimple_mulEquiv Subgroup.topEquiv hK.2.2
      rcases isSubnormal_le_center_or_eq_top_of_isQuasisimple hQ U hU with hUc | hUt
      · right
        rw [hKtop]
        exact (Subgroup.commutator_top_left_eq_bot_iff_le_center (H := U)).mpr hUc
      · left
        rw [hUt]
        exact le_top
    -- F3: proper normal overgroups N ∋ K and M ∋ U
    have hKsn : K.IsSubnormal := isSubnormal_of_isComponentOf_top hK
    rcases Subgroup.IsSubnormal.lt_normal hKsn with hKtop' | ⟨N, hNnorm, hKN, hNlt⟩
    · exact False.elim (hKtop hKtop')
    rcases Subgroup.IsSubnormal.lt_normal hU with hUtop' | ⟨M, hMnorm, hUM, hMlt⟩
    · exact False.elim (hUtop hUtop')
    let : N.Normal := hNnorm
    let : M.Normal := hMnorm
    -- F4: U₁ := ⁅U, K⁆ lies in N ∩ M; G₁ := N ⊓ N_G(U₁)
    let U₁ : Subgroup H := ⁅U, K⁆
    have hU₁N : U₁ ≤ N := by
      simpa [U₁] using
        ((Subgroup.commutator_mono le_top hKN).trans
          (Subgroup.commutator_le_right (H₁ := (⊤ : Subgroup H)) (H₂ := N)))
    have hU₁M : U₁ ≤ M := by
      simpa [U₁] using
        ((Subgroup.commutator_mono hUM le_top).trans
          (Subgroup.commutator_le_left (H₁ := M) (H₂ := (⊤ : Subgroup H))))
    let G₁ : Subgroup H := N ⊓ Subgroup.normalizer (U₁ : Set H)
    have hKG₁ : K ≤ G₁ := by
      refine le_inf hKN ?_
      simpa [U₁] using (Subgroup.normalizer_commutator_ge_right U K)
    have hU₁G₁ : U₁ ≤ G₁ := by
      refine le_inf hU₁N ?_
      exact Subgroup.le_normalizer (H := U₁)
    have hU₁normal : (U₁.subgroupOf G₁).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (H := G₁) (N := U₁) inf_le_right
    have hG₁lt : G₁ < (⊤ : Subgroup H) := lt_of_le_of_lt inf_le_left hNlt
    have hG₁card : Nat.card G₁ < Nat.card H := natCard_lt_of_lt_top hG₁lt
    have hG₁card' : Nat.card G₁ < n := by
      simpa [hcard] using hG₁card
    have hKG₁comp : IsComponentOf (K.subgroupOf G₁) (⊤ : Subgroup G₁) :=
      isComponentOf_subgroupOf hK hKG₁
    have hrecG₁ : K.subgroupOf G₁ ≤ U₁.subgroupOf G₁ ∨
        ⁅K.subgroupOf G₁, U₁.subgroupOf G₁⁆ = ⊥ :=
      ih (Nat.card G₁) hG₁card' (↥G₁) rfl hKG₁comp hU₁normal.isSubnormal
    rcases hrecG₁ with hKU₁le | hKU₁comm
    · -- F6: K ≤ U₁, recursion in M
      have hKU₁ : K ≤ U₁ :=
        (subgroupOf_le_subgroupOf_iff_of_le (A := K) (B := U₁) (H := G₁)
          hKG₁ hU₁G₁).mp hKU₁le
      have hKM : K ≤ M := hKU₁.trans hU₁M
      have hKMcomp : IsComponentOf (K.subgroupOf M) (⊤ : Subgroup M) :=
        isComponentOf_subgroupOf hK hKM
      have hUsubM : (U.subgroupOf M).IsSubnormal := hU.subgroupOf
      have hMcard : Nat.card M < Nat.card H := natCard_lt_of_lt_top hMlt
      have hMcard' : Nat.card M < n := by
        simpa [hcard] using hMcard
      have hrecM : K.subgroupOf M ≤ U.subgroupOf M ∨
          ⁅K.subgroupOf M, U.subgroupOf M⁆ = ⊥ :=
        ih (Nat.card M) hMcard' (↥M) rfl hKMcomp hUsubM
      rcases hrecM with hKMU | hcommM
      · left
        exact (subgroupOf_le_subgroupOf_iff_of_le (A := K) (B := U) (H := M)
          hKM hUM).mp hKMU
      · right
        exact (commutator_subgroupOf_eq_bot_iff_of_le (A := K) (B := U) (H := M)
          hKM hUM).mp hcommM
    · -- F5: ⁅K, U₁⁆ = ⊥, Three-Subgroups with (K, K, U), perfectness
      have hKU₁ : ⁅K, U₁⁆ = ⊥ :=
        (commutator_subgroupOf_eq_bot_iff_of_le (A := K) (B := U₁) (H := G₁)
          hKG₁ hU₁G₁).mp hKU₁comm
      have h₁ : ⁅⁅K, U⁆, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm (H₁ := K) (H₂ := U)]
        rw [Subgroup.commutator_comm (H₁ := ⁅U, K⁆) (H₂ := K)]
        exact hKU₁
      have h₂ : ⁅⁅U, K⁆, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm (H₁ := ⁅U, K⁆) (H₂ := K)]
        exact hKU₁
      have hrot : ⁅⁅K, K⁆, U⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := U) h₁ h₂
      have hPerf : Group.IsPerfect (↥K) := (Group.isPerfect_def).2 hK.2.2.2.1
      have hKK : ⁅K, K⁆ = K := (Subgroup.isPerfect_iff).mp hPerf
      right
      simpa [hKK] using hrot
  exact hP (Nat.card G) G rfl hK hU

/-- KS 6.5.2 for normal subgroups: a normal subgroup of the ambient group
either contains the component or is centralized by it. -/
public theorem component_le_or_commutator_eq_bot_of_normal
    {G : Type u} [Group G] [Finite G]
    {K N : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G))
    (hN : N.Normal) :
    K ≤ N ∨ ⁅K, N⁆ = ⊥ :=
  component_le_or_commutator_eq_bot hK hN.isSubnormal

/-- Distinct components of the ambient group commute (KS 6.5.3). -/
public theorem component_commute_of_ne
    {G : Type u} [Group G] [Finite G]
    {E₁ E₂ : Subgroup G}
    (hE₁ : IsComponentOf E₁ (⊤ : Subgroup G))
    (hE₂ : IsComponentOf E₂ (⊤ : Subgroup G))
    (hne : E₁ ≠ E₂) :
    ⁅E₁, E₂⁆ = ⊥ := by
  rcases component_le_or_commutator_eq_bot hE₁ (isSubnormal_of_isComponentOf_top hE₂) with
      hE₁E₂ | hcomm₁
  · rcases component_le_or_commutator_eq_bot hE₂ (isSubnormal_of_isComponentOf_top hE₁) with
        hE₂E₁ | hcomm₂
    · exfalso
      exact hne (le_antisymm hE₁E₂ hE₂E₁)
    · exact (Subgroup.commutator_comm (H₁ := E₁) (H₂ := E₂)).trans hcomm₂
  · exact hcomm₁

/-! ## Infra: finite nilpotent subgroups have all subgroups subnormal -/

/-- The normalizer condition: every proper subgroup is properly contained in
its normalizer.  In a finite group this is equivalent to "every subgroup is
subnormal", proved below. -/
public theorem isSubnormal_of_normalizerCondition {G : Type u} [Group G] [Finite G]
    (hNC : NormalizerCondition G) (H : Subgroup G) : H.IsSubnormal := by
  classical
  -- strong induction on the index of `H`
  let P : ℕ → Prop := fun n => ∀ H : Subgroup G, H.index = n → H.IsSubnormal
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih H hn
    by_cases htop : H = ⊤
    · rw [htop]
      exact Subgroup.IsSubnormal.top (G := G)
    · let N := Subgroup.normalizer (H : Set G)
      have hHltN : H < N := hNC H (lt_top_iff_ne_top.mpr htop)
      have hle : H ≤ N := le_of_lt hHltN
      have hN : (H.subgroupOf N).Normal := by
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer (h := hle)).2 le_rfl
      have hind : N.index < H.index := by
        have hrel : H.relIndex N * N.index = H.index :=
          Subgroup.relIndex_mul_index (h := hle)
        have hrel_ge : 2 ≤ H.relIndex N := by
          have hne_top : H.subgroupOf N ≠ ⊤ := by
            intro htopN
            have hNleH : N ≤ H := (Subgroup.subgroupOf_eq_top (H := H) (K := N)).1 htopN
            exact (ne_of_lt hHltN) (le_antisymm hle hNleH)
          have hone : 1 < H.relIndex N :=
            Subgroup.one_lt_index_of_ne_top (H := H.subgroupOf N) hne_top
          exact hone
        have hindN : 1 ≤ N.index := by
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N)))
        have hb : N.index < 2 * N.index := by omega
        have hb' : 2 * N.index ≤ H.relIndex N * N.index := Nat.mul_le_mul_right N.index hrel_ge
        calc
          N.index < 2 * N.index := hb
          _ ≤ H.relIndex N * N.index := hb'
          _ = H.index := hrel
      have hind' : N.index < n := by
        rw [← hn]
        exact hind
      exact Subgroup.IsSubnormal.step H N hle (ih N.index hind' N rfl) hN
  exact hP H.index H rfl

/-- In a finite nilpotent group, every subgroup is subnormal. -/
public theorem isSubnormal_of_isNilpotent {G : Type u} [Group G] [Finite G]
    (hG : Group.IsNilpotent G) (H : Subgroup G) : H.IsSubnormal := by
  have : Group.IsNilpotent G := hG
  exact isSubnormal_of_normalizerCondition (Group.normalizerCondition_of_isNilpotent) H

/-- In a finite nilpotent ambient subgroup `F`, every ambient subgroup `T ≤ F`
is subnormal in `F`. -/
public theorem isSubnormal_of_nilpotent {G : Type u} [Group G] [Finite G]
    {F : Subgroup G} (hF : Group.IsNilpotent F) (T : Subgroup G) (_hTF : T ≤ F) :
    (T.subgroupOf F).IsSubnormal := by
  have : Group.IsNilpotent (↥F) := hF
  exact isSubnormal_of_isNilpotent (G := (↥F)) (by infer_instance) (T.subgroupOf F)

/-! ## Infra: joins with a centralizing subgroup preserve subnormality -/

/-- If `H` is normal in `K` and `E` centralizes `K`, then `H ⊔ E` is normal
in `K ⊔ E` (element-level proof via closure induction). -/
public theorem isNormalIn_sup_of_commutator {G : Type u} [Group G]
    {H K E : Subgroup G} (hHKle : H ≤ K) (hHK : (H.subgroupOf K).Normal)
    (hE : ⁅E, K⁆ = ⊥) : IsNormalIn (H ⊔ E) (K ⊔ E) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (sup_le_sup hHKle le_rfl) hx
  · -- show `K ⊔ E ≤ N_G(H ⊔ E)` and apply
    have hKleN : K ≤ Subgroup.normalizer (((H ⊔ E) : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro k hk y hy
      rw [Subgroup.sup_eq_closure] at hy
      refine (Subgroup.closure_induction''
        (p := fun v _hv => k * v * k⁻¹ ∈ H ⊔ E) ?_ ?_ ?_ ?_) hy
      · intro v hv
        rcases hv with hvH | hvE
        · -- v ∈ H: normality of H in K
          have hvK : v ∈ K := hHKle hvH
          have hvHK : (⟨v, hvK⟩ : ↥K) ∈ H.subgroupOf K := by
            rw [Subgroup.mem_subgroupOf]
            exact hvH
          have hkv : k * v * k⁻¹ ∈ H := by
            have hz : (⟨k, hk⟩ : ↥K) * (⟨v, hvK⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹ ∈ H.subgroupOf K :=
              hHK.conj_mem (⟨v, hvK⟩ : ↥K) hvHK (⟨k, hk⟩ : ↥K)
            exact (Subgroup.mem_subgroupOf).1 hz
          exact (le_sup_left : H ≤ H ⊔ E) hkv
        · -- v ∈ E: k centralizes E
          have hKleC : K ≤ Subgroup.centralizer (E : Set G) := by
            rw [← Subgroup.le_centralizer_iff]
            exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hE
          have hcomm : v * k = k * v :=
            (Subgroup.mem_centralizer_iff (g := k) (s := (E : Set G))).1 (hKleC hk) v hvE
          have hvHE : v ∈ H ⊔ E := (le_sup_right : E ≤ H ⊔ E) hvE
          rw [← hcomm]
          simpa using hvHE
      · intro v hv
        rcases hv with hvH | hvE
        · have hvK : v ∈ K := hHKle hvH
          have hkv : k * v⁻¹ * k⁻¹ ∈ H := by
            have hz : (⟨k, hk⟩ : ↥K) * (⟨v⁻¹, K.inv_mem hvK⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹ ∈
                H.subgroupOf K :=
              hHK.conj_mem (⟨v⁻¹, K.inv_mem hvK⟩ : ↥K)
                (by rw [Subgroup.mem_subgroupOf]; exact H.inv_mem hvH) (⟨k, hk⟩ : ↥K)
            exact (Subgroup.mem_subgroupOf).1 hz
          exact (le_sup_left : H ≤ H ⊔ E) hkv
        · have hKleC : K ≤ Subgroup.centralizer (E : Set G) := by
            rw [← Subgroup.le_centralizer_iff]
            exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hE
          have hcomm : v⁻¹ * k = k * v⁻¹ :=
            (Subgroup.mem_centralizer_iff (g := k) (s := (E : Set G))).1 (hKleC hk) v⁻¹ (E.inv_mem hvE)
          have hvHE : v⁻¹ ∈ H ⊔ E := (le_sup_right : E ≤ H ⊔ E) (E.inv_mem hvE)
          rw [← hcomm]
          simpa using hvHE
      · simp
      · intro a b _ha _hb hpa hpb
        have h1 : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
        rw [h1]
        exact (H ⊔ E).mul_mem hpa hpb
    have hEleN : E ≤ Subgroup.normalizer (((H ⊔ E) : Subgroup G) : Set G) :=
      le_sup_right.trans (H ⊔ E).le_normalizer
    exact (Subgroup.le_normalizer_iff (H := (K ⊔ E)) (K := (H ⊔ E))).1
      (sup_le hKleN hEleN)

/-- If `H` is normal in `K` (relative) and `K ≤ L`, then `H.subgroupOf L` is
normal in `K.subgroupOf L`. -/
private theorem subgroupOf_normal_of_isNormalIn {G : Type u} [Group G]
    {H K L : Subgroup G} (hHK : IsNormalIn H K) (_hKL : K ≤ L) :
    ((H.subgroupOf L).subgroupOf (K.subgroupOf L)).Normal := by
  refine ⟨?conj_mem⟩
  intro n hn g
  have hnH : ((n : ↥L) : G) ∈ H :=
    (Subgroup.mem_subgroupOf).mp (Subgroup.mem_subgroupOf.mp hn)
  have hnK : ((n : ↥L) : G) ∈ K := (Subgroup.mem_subgroupOf).mp n.2
  have hgK : ((g : ↥L) : G) ∈ K := (Subgroup.mem_subgroupOf).mp g.2
  have hconj : (g : ↥L).1 * (n : ↥L).1 * (g : ↥L).1⁻¹ ∈ H :=
    hHK.2 (g : ↥L).1 hgK (n : ↥L).1 hnH
  rw [Subgroup.mem_subgroupOf]
  rw [Subgroup.mem_subgroupOf]
  exact hconj

/-- The image of a normal subgroup under an injective map is normal in the
image of the ambient subgroup. -/
private theorem subgroupOf_normal_of_map {G : Type u} [Group G] {F : Subgroup G}
    {H K : Subgroup (↥F)} (hHKle : H ≤ K) (hHK : (H.subgroupOf K).Normal) :
    ((H.map F.subtype).subgroupOf (K.map F.subtype)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (h := Subgroup.map_mono (f := F.subtype) hHKle)]
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  rcases (Subgroup.mem_map).1 hx with ⟨kx, hkx, rfl⟩
  rcases (Subgroup.mem_map).1 hy with ⟨ky, hky, rfl⟩
  have hkyK : ky ∈ K := hHKle hky
  have hkyHK : (⟨ky, hkyK⟩ : ↥K) ∈ H.subgroupOf K := by
    rw [Subgroup.mem_subgroupOf]
    exact hky
  have hconj : kx * ky * kx⁻¹ ∈ H := by
    have hzc : (⟨kx, hkx⟩ : ↥K) * (⟨ky, hkyK⟩ : ↥K) * (⟨kx, hkx⟩ : ↥K)⁻¹ ∈ H.subgroupOf K :=
      hHK.conj_mem (⟨ky, hkyK⟩ : ↥K) hkyHK (⟨kx, hkx⟩ : ↥K)
    exact (Subgroup.mem_subgroupOf).1 hzc
  exact Subgroup.mem_map.mpr ⟨kx * ky * kx⁻¹, hconj, by simp⟩

/-- If `T` is subnormal in `F` and `E` centralizes `F`, then `T ⊔ E` is
subnormal in `F ⊔ E`. -/
public theorem isSubnormal_sup_of_centralizing {G : Type u} [Group G]
    {T F E : Subgroup G} (hTF : T ≤ F) (hT : (T.subgroupOf F).IsSubnormal)
    (hE : ⁅E, F⁆ = ⊥) : ((T ⊔ E).subgroupOf (F ⊔ E)).IsSubnormal := by
  classical
  let P : Subgroup (↥F) → Prop := fun U =>
    ((U.map F.subtype ⊔ E).subgroupOf (F ⊔ E)).IsSubnormal
  have hmain : ∀ U : Subgroup (↥F), U.IsSubnormal → P U := by
    intro U hU
    induction hU with
    | top =>
        have hmap : (⊤ : Subgroup (↥F)).map F.subtype = F := by
          apply le_antisymm
          · intro y hy
            rcases (Subgroup.mem_map).1 hy with ⟨u, _hu, rfl⟩
            exact u.2
          · intro x hx
            exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
        simp [P, hmap]
    | step H K h_le hK hN ih =>
        have hmap_le : H.map F.subtype ≤ K.map F.subtype :=
          Subgroup.map_mono (f := F.subtype) h_le
        have hNmap : ((H.map F.subtype).subgroupOf (K.map F.subtype)).Normal :=
          subgroupOf_normal_of_map h_le hN
        have hKmap_le_F : K.map F.subtype ≤ F := by
          intro y hy
          rcases (Subgroup.mem_map).1 hy with ⟨u, _hu, rfl⟩
          exact u.2
        have hEcentral : ⁅E, K.map F.subtype⁆ = ⊥ := by
          have hle : ⁅E, K.map F.subtype⁆ ≤ ⁅E, F⁆ :=
            Subgroup.commutator_mono le_rfl hKmap_le_F
          simpa [hE] using hle
        have hNsup : IsNormalIn (H.map F.subtype ⊔ E) (K.map F.subtype ⊔ E) :=
          isNormalIn_sup_of_commutator hmap_le hNmap hEcentral
        have hKleL : K.map F.subtype ⊔ E ≤ F ⊔ E :=
          sup_le (hKmap_le_F.trans le_sup_left) le_sup_right
        have hN' : (((H.map F.subtype ⊔ E).subgroupOf (F ⊔ E)).subgroupOf
            ((K.map F.subtype ⊔ E).subgroupOf (F ⊔ E))).Normal :=
          subgroupOf_normal_of_isNormalIn hNsup hKleL
        have hle' : (H.map F.subtype ⊔ E).subgroupOf (F ⊔ E) ≤
            (K.map F.subtype ⊔ E).subgroupOf (F ⊔ E) :=
          Subgroup.subgroupOf_mono (F ⊔ E) (sup_le_sup hmap_le le_rfl)
        exact Subgroup.IsSubnormal.step _ _ hle' ih hN'
  have hmap_eq : (T.subgroupOf F).map F.subtype = T := by
    apply le_antisymm
    · intro y hy
      rcases (Subgroup.mem_map).1 hy with ⟨u, hu, rfl⟩
      exact (Subgroup.mem_subgroupOf).1 hu
    · intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hTF hx⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩
  simpa [P, hmap_eq] using hmain (T.subgroupOf F) hT

/-! ## Infra: a quasisimple group is not nilpotent -/

/-- A quasisimple group is not nilpotent (a nontrivial perfect group is not
solvable, and nilpotent groups are solvable). -/
public theorem not_isNilpotent_of_isQuasisimple {G : Type u} [Group G] (E : Subgroup G)
    (hE : IsQuasisimple E) : ¬ Group.IsNilpotent E := by
  have : Nontrivial E := hE.1
  have : Group.IsPerfect E := (Group.isPerfect_def).2 hE.2.1
  exact Group.IsPerfect.not_isNilpotent E

/-! ## Infra: decomposing the join of a centralizing pair -/

/-- If `E` centralizes `F`, every element of `F ⊔ E` decomposes as `f · e`
with `f ∈ F`, `e ∈ E`. -/
private lemma mem_sup_decompose_of_centralizes {G : Type u} [Group G]
    {F E : Subgroup G} {x : G} (hx : x ∈ F ⊔ E)
    (hE : E ≤ Subgroup.centralizer (F : Set G)) :
    ∃ f ∈ F, ∃ e ∈ E, x = f * e := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro v hv
    rcases hv with hvF | hvE
    · exact ⟨v, hvF, 1, E.one_mem, by simp⟩
    · exact ⟨1, F.one_mem, v, hvE, by simp⟩
  · intro v hv
    rcases hv with hvF | hvE
    · exact ⟨v⁻¹, F.inv_mem hvF, 1, E.one_mem, by simp⟩
    · exact ⟨1, F.one_mem, v⁻¹, E.inv_mem hvE, by simp⟩
  · exact ⟨1, F.one_mem, 1, E.one_mem, by simp⟩
  · intro a b _ha _hb hpa hpb
    rcases hpa with ⟨f, hf, e, he, rfl⟩
    rcases hpb with ⟨f', hf', e', he', rfl⟩
    have hcomm : e * f' = f' * e :=
      ((Subgroup.mem_centralizer_iff (g := e) (s := (F : Set G))).1 (hE he) f' hf').symm
    refine ⟨f * f', F.mul_mem hf hf', e * e', E.mul_mem he he', ?_⟩
    calc
      (f * e) * (f' * e') = f * ((e * f') * e') := by simp [mul_assoc]
      _ = f * ((f' * e) * e') := by rw [hcomm]
      _ = (f * f') * (e * e') := by simp [mul_assoc]

/-! ## Layer-centralizes-Fitting chain (KS 6.5.2 applied to `F(A)`) -/

/-- A component of the finite group `H` centralizes its Fitting subgroup
(KS 6.5.2 applied to the normal subgroup `F(H)`; `E ≤ F(H)` is impossible
since `E` is perfect and non-nilpotent). -/
public theorem component_centralizes_internal_fitting
    {H : Type u} [Group H] [Finite H]
    {E : Subgroup H} (hE : IsComponentOf E (⊤ : Subgroup H)) :
    ⁅E, fittingSubgroup H⁆ = ⊥ := by
  have hFnorm : (fittingSubgroup H).Normal := fittingSubgroup_normal (G := H)
  rcases component_le_or_commutator_eq_bot hE hFnorm.isSubnormal with hEfit | hcomm
  · exfalso
    -- E ≤ F(H) would make E nilpotent (subgroup of a nilpotent subgroup)
    have hEnil : Group.IsNilpotent E := by
      have hFnil : Group.IsNilpotent (fittingSubgroup H) := by infer_instance
      have hrc : ∃ n, (fittingSubgroup H).lowerCentralSeries n = ⊥ :=
        (Subgroup.isNilpotent_iff_lowerCentralSeries (S := fittingSubgroup H)).mp hFnil
      rcases hrc with ⟨n, hFbot⟩
      have hEm : E.lowerCentralSeries n ≤ (fittingSubgroup H).lowerCentralSeries n :=
        Subgroup.lowerCentralSeries_mono (n := n) hEfit
      have hEbot : E.lowerCentralSeries n = ⊥ := by
        rw [hFbot] at hEm
        exact le_bot_iff.mp hEm
      exact (Subgroup.isNilpotent_iff_lowerCentralSeries (S := E)).mpr ⟨n, hEbot⟩
    exact not_isNilpotent_of_isQuasisimple E hE.2.2 hEnil
  · exact hcomm

/-- A component of `A` centralizes `F(A)` (KS 6.5.2 in the group `A`,
mapped back through `A.subtype`). -/
public theorem component_centralizes_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    {A E : Subgroup G} (hE : IsComponentOf E A) :
    ⁅E, fittingSubgroupOf A⁆ = ⊥ := by
  have hE₀ : IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
    ⟨le_top, hE.2.1.subgroupOf,
      isQuasisimple_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.2⟩
  have hcomm₀ : ⁅E.subgroupOf A, fittingSubgroup (↥A)⁆ = ⊥ :=
    component_centralizes_internal_fitting hE₀
  have hmap : (⁅E.subgroupOf A, fittingSubgroup (↥A)⁆).map A.subtype = ⊥ := by
    rw [hcomm₀]
    exact Subgroup.map_bot A.subtype
  have hm : ⁅(E.subgroupOf A).map A.subtype, (fittingSubgroup (↥A)).map A.subtype⁆ = ⊥ := by
    rw [← Subgroup.map_commutator (H₁ := E.subgroupOf A) (H₂ := fittingSubgroup (↥A))
      (f := A.subtype)]
    exact hmap
  have hE₀m : (E.subgroupOf A).map A.subtype = E := Subgroup.map_subgroupOf_eq_of_le hE.1
  have hF₀m : (fittingSubgroup (↥A)).map A.subtype = fittingSubgroupOf A := by rfl
  simpa [hE₀m, hF₀m] using hm

/-- The layer of `A` centralizes its Fitting subgroup:
`⁅E(A), F(A)⁆ = ⊥` (KS 6.5.2/6.5.3). -/
public theorem layer_centralizes_fitting {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) : ⁅componentLayerOf A, fittingSubgroupOf A⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rw [componentLayerOf]
  refine sSup_le ?_
  intro E hE
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (component_centralizes_fittingSubgroupOf hE))

/-- The control-core bridge from `NormalizerControlledBy`, conditional on the
classical layer-centralizes-Fitting fact
`⁅componentLayerOf A, fittingSubgroupOf A⁆ = ⊥`.

From a witness `X` of `NormalizerControlledBy A B` put
`S := F*(A) ⊓ N_G(X)`:

1. `X ≤ S` (every subgroup normalizes itself, `X ≤ F(A) ≤ F*(A)`), so
   `S ≠ ⊥` from `X ≠ ⊥`;
2. `S ≤ F*(A)` by definition and `S ≤ B` since `S ≤ N_G(X) ≤ B`;
3. `S` is subnormal in `F*(A)`: writing `F := F(A)`, `E := E(A)`, the
   commutator hypothesis gives `E ≤ C_G(X) ≤ N_G(X)`, hence by the modular
   law `S = (F ⊓ N_G(X)) ⊔ E`; `F ⊓ N_G(X)` is subnormal in `F` (finite
   nilpotent), and the join with the centralizing `E` preserves
   subnormality (`isSubnormal_sup_of_centralizing`);
4. `S` is self-centralizing in `F*(A)`: `c ∈ F*(A) ⊓ C_G(S)` centralizes
   `X` (since `X ≤ S`) hence lies in `N_G(X)`, so `c ∈ S`.
-/
private theorem controlCore_of_normalizerControlledBy_of_commutator
    {G : Type u} [Group G] [Finite G]
    {A B : Subgroup G} (h : NormalizerControlledBy A B)
    (hEF : ⁅componentLayerOf A, fittingSubgroupOf A⁆ = ⊥) : ControlCore A B := by
  classical
  rcases h with ⟨X, hXne, hXF, hNXB⟩
  let F : Subgroup G := fittingSubgroupOf (G := G) A
  let E : Subgroup G := componentLayerOf A
  let K : Subgroup G := generalizedFittingSubgroupOf A
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let S : Subgroup G := K ⊓ N
  -- X ≤ S
  have hXS : X ≤ S := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact (hXF.trans (le_sup_left : F ≤ K)) hx
    · exact X.le_normalizer hx
  -- S ≠ ⊥
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hXbot : X ≤ ⊥ := by
      intro x hx
      have hxS : x ∈ S := hXS hx
      simpa [S, hSbot] using hxS
    exact hXne (le_bot_iff.mp hXbot)
  -- S ≤ F*(A) and S ≤ B
  have hSK : S ≤ K := inf_le_left
  have hSB : S ≤ B := by
    intro x hx
    exact hNXB hx.2
  -- E ≤ N_G(X): E centralizes F ⊇ X
  have hEFle : E ≤ Subgroup.centralizer (F : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hEF
  have hEN : E ≤ N := by
    exact (hEFle.trans (Subgroup.centralizer_le (show (X : Set G) ⊆ (F : Set G) from hXF))).trans
      (Subgroup.centralizer_le_normalizer (X : Set G))
  -- S = (F ⊓ N) ⊔ E: both inclusions, elementwise
  have hmod : (F ⊔ E) ⊓ N = E ⊔ (F ⊓ N) := by
    apply le_antisymm
    · intro x hx
      rcases mem_sup_decompose_of_centralizes hx.1 hEFle with ⟨f, hf, e, he, rfl⟩
      have hfN : f ∈ N := by
        have hxe : (f * e) * e⁻¹ ∈ N := N.mul_mem hx.2 (N.inv_mem (hEN he))
        simpa using hxe
      have hcomm : f * e = e * f :=
        (Subgroup.mem_centralizer_iff (g := e) (s := (F : Set G))).1 (hEFle he) f hf
      have hmem : e * f ∈ E ⊔ (F ⊓ N) :=
        (Subgroup.mul_mem_sup he (show f ∈ F ⊓ N from ⟨hf, hfN⟩))
      simpa [hcomm] using hmem
    · exact
        le_inf
          (sup_le (le_sup_right : E ≤ F ⊔ E)
            ((inf_le_left : F ⊓ N ≤ F).trans (le_sup_left : F ≤ F ⊔ E)))
          (sup_le hEN inf_le_right)
  have hS_eq : S = (F ⊓ N) ⊔ E := by
    calc
      S = (F ⊔ E) ⊓ N := by simp [S, K, F, E, generalizedFittingSubgroupOf]
      _ = E ⊔ (F ⊓ N) := hmod
      _ = (F ⊓ N) ⊔ E := by rw [sup_comm]
  -- (F ⊓ N) subnormal in F: F is finite nilpotent
  have hFnil : Group.IsNilpotent F := by
    have : Group.IsNilpotent (fittingSubgroup (↥A)) := by infer_instance
    change Group.IsNilpotent ((fittingSubgroup (↥A)).map A.subtype)
    let e : fittingSubgroup (↥A) ≃* (fittingSubgroup (↥A)).map A.subtype :=
      Subgroup.equivMapOfInjective (f := A.subtype) (fittingSubgroup (↥A)) A.subtype_injective
    exact Group.nilpotent_of_mulEquiv e
  have hTsub : ((F ⊓ N).subgroupOf F).IsSubnormal :=
    isSubnormal_of_nilpotent hFnil (F ⊓ N) inf_le_left
  -- join with centralizing E
  have hTsubE : (((F ⊓ N) ⊔ E).subgroupOf (F ⊔ E)).IsSubnormal :=
    isSubnormal_sup_of_centralizing inf_le_left hTsub hEF
  -- S subnormal in K
  have hSsub : (S.subgroupOf K).IsSubnormal := by
    rw [hS_eq]
    rw [show K = F ⊔ E by simp [K, F, E, generalizedFittingSubgroupOf]]
    exact hTsubE
  -- self-centralizing
  have hCS : K ⊓ Subgroup.centralizer (S : Set G) ≤ S := by
    intro c hc
    have hcK : c ∈ K := hc.1
    have hcC : c ∈ Subgroup.centralizer (S : Set G) := hc.2
    have hcX : c ∈ Subgroup.centralizer (X : Set G) :=
      (Subgroup.centralizer_le (show (X : Set G) ⊆ (S : Set G) from hXS)) hcC
    have hcN : c ∈ N := (Subgroup.centralizer_le_normalizer (X : Set G)) hcX
    exact ⟨hcK, hcN⟩
  exact ⟨S, hSne, hSK, hSB, hSsub, hCS⟩

/-- The control-core bridge from `NormalizerControlledBy`, per the classical
fact that the layer of `A` centralizes `F(A)` (KS 6.5.2/6.5.3). -/
public theorem controlCore_of_normalizerControlledBy {G : Type u} [Group G] [Finite G]
    {A B : Subgroup G} (h : NormalizerControlledBy A B) :
    ControlCore A B :=
  controlCore_of_normalizerControlledBy_of_commutator h (layer_centralizes_fitting A)

/-! ## Number theory helpers for the one-prime branch -/

/-- If all prime divisors of `n` equal `p`, then `n` is a power of `p`. -/
public lemma exists_pow_of_primeFactors_subset_singleton {n : ℕ} (hn : n ≠ 0) {p : ℕ}
    (hp : ∀ r : ℕ, r ∈ n.primeFactors → r = p) : ∃ k : ℕ, n = p ^ k := by
  let S : Finset ℕ := n.primeFactors
  have hmain : n = (p ^ n.factorization p) ^ S.card := by
    calc
      n = ∏ r ∈ S, r ^ n.factorization r := by
        simpa [S] using (Nat.prod_primeFactors_pow_factorization hn)
      _ = ∏ r ∈ S, p ^ n.factorization p := by
        apply Finset.prod_congr rfl
        intro r hr
        have hrp : r = p := hp r hr
        simp [hrp]
      _ = (p ^ n.factorization p) ^ S.card := by
        simp
  exact ⟨n.factorization p * S.card, by
    rw [pow_mul]
    exact hmain⟩

/-- `F*(H)` nontrivial implies its set of prime divisors is nonempty. -/
public theorem primesOfOrder_nonempty_of_ne_bot {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : H ≠ ⊥) : (primesOfOrder H).Nonempty := by
  have h2 : 2 ≤ Nat.card (↥H) := by
    have h1 : 1 < Nat.card (↥H) := (Subgroup.one_lt_card_iff_ne_bot (H := H)).2 hH
    exact Nat.succ_le_of_lt h1
  have hne : (Nat.card (↥H)).primeFactors ≠ ∅ := by
    intro h
    have h01 : Nat.card (↥H) = 0 ∨ Nat.card (↥H) = 1 := Nat.primeFactors_eq_empty.mp h
    omega
  have hnp : ((Nat.card (↥H)).primeFactors).Nonempty := (Finset.nonempty_iff_ne_empty).2 hne
  rcases hnp with ⟨p, hp⟩
  exact ⟨p, by simpa [primesOfOrder] using hp⟩

/-- The set of prime divisors of the order of a subgroup grows with the
subgroup. -/
public theorem primesOfOrder_subset_of_le {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (hHK : H ≤ K) : primesOfOrder H ⊆ primesOfOrder K := by
  intro q hq
  have hqpf : q ∈ (Nat.card (↥H)).primeFactors := by simpa [primesOfOrder] using hq
  have hdvd : Nat.card (↥H) ∣ Nat.card (↥K) := by
    have hdvd' : Nat.card ↥(H.subgroupOf K) ∣ Nat.card (↥K) :=
      Subgroup.card_subgroup_dvd_card (s := H.subgroupOf K)
    have hcard : Nat.card ↥H = Nat.card ↥(H.subgroupOf K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).symm.toEquiv
    rwa [hcard]
  have hpdvd : q ∣ Nat.card (↥K) := (Nat.dvd_of_mem_primeFactors hqpf).trans hdvd
  have hqmem : q ∈ (Nat.card (↥K)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hqpf, hpdvd, Nat.card_pos.ne'⟩
  simpa [primesOfOrder] using hqmem

/-- A subgroup whose order has a single prime divisor `p` is a `p`-group. -/
public theorem isPGroup_of_primeFactors_subset_singleton {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {p : ℕ} (_hp : p.Prime)
    (hpf : ∀ r : ℕ, r ∈ (Nat.card (↥H)).primeFactors → r = p) : IsPGroup p H := by
  have hneq : Nat.card (↥H) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, hk⟩ := exists_pow_of_primeFactors_subset_singleton hneq (p := p) hpf
  exact IsPGroup.of_card hk

/-- If `F*(M)` is a `q`-group, the component layer of `M` is trivial. -/
public theorem componentLayerOf_eq_bot_of_isPGroup {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {q : ℕ} (hq : q.Prime)
    (hF : IsPGroup q (generalizedFittingSubgroupOf M)) :
    componentLayerOf M = ⊥ := by
  apply le_bot_iff.mp
  rw [componentLayerOf]
  refine sSup_le ?_
  intro E hE
  have hEF : E ≤ generalizedFittingSubgroupOf M := by
    refine le_trans (b := componentLayerOf M) ?_ ?_
    · exact (le_sSup (s := {E' : Subgroup G | IsComponentOf E' M}) (a := E) hE)
    · exact (le_sup_right : componentLayerOf M ≤ fittingSubgroupOf M ⊔ componentLayerOf M)
  have hEq : IsPGroup q E := IsPGroup.to_le hF hEF
  have : Fact q.Prime := ⟨hq⟩
  have hEnil : Group.IsNilpotent E := hEq.isNilpotent
  exact False.elim (not_isNilpotent_of_isQuasisimple E hE.2.2 hEnil)

/-- The Fitting subgroup of a subgroup is normal in that subgroup. -/
public theorem fittingSubgroupOf_isNormalIn {G : Type u} [Group G] (A : Subgroup G) :
    IsNormalIn (fittingSubgroupOf (G := G) A) A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ A
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥A) * f * (⟨h, hh⟩ : ↥A)⁻¹ ∈ fittingSubgroup (↥A) := by
      exact (fittingSubgroup_normal (G := ↥A)).conj_mem (n := f) hf (g := ⟨h, hh⟩)
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥A) * f * (⟨h, hh⟩ : ↥A)⁻¹, hconj, ?_⟩
    rw [hfk]
    simp
    exact hfk

/-- If `F*(M)` is a `q`-group (for prime `q`), then `F(M) = O_q(M)`: the
layer is trivial and the Fitting subgroup is both contained in and contains
the largest normal `q`-subgroup. -/
public theorem qCoreOf_eq_fittingSubgroupOf_of_isPGroup {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {q : ℕ} (hq : q.Prime)
    (hF : IsPGroup q (generalizedFittingSubgroupOf M)) :
    qCoreOf M q = fittingSubgroupOf M := by
  have : Fact q.Prime := ⟨hq⟩
  -- F(M) ≤ F*(M) is a q-group
  have hFfit : IsPGroup q (fittingSubgroupOf M) :=
    IsPGroup.to_le hF (le_sup_left : fittingSubgroupOf M ≤ generalizedFittingSubgroupOf M)
  -- fittingSubgroup (↥M) ≃* fittingSubgroupOf M
  have hFfit' : IsPGroup q (fittingSubgroup (↥M)) := by
    exact hFfit.of_equiv
      (Subgroup.equivMapOfInjective (fittingSubgroup (↥M)) M.subtype M.subtype_injective).symm
  apply le_antisymm
  · -- O_q(M) ≤ F(M)
    have hle : pCore q (↥M) ≤ fittingSubgroup (↥M) := pCore_le_fitting (G := ↥M) q
    exact Subgroup.map_mono (f := M.subtype) hle
  · -- F(M) ≤ O_q(M)
    have hle : fittingSubgroup (↥M) ≤ pCore q (↥M) := by
      exact le_sSup (show fittingSubgroup (↥M) ∈
        {K : Subgroup (↥M) | K.Normal ∧ IsPGroup q K} from ⟨inferInstance, hFfit'⟩)
    exact Subgroup.map_mono (f := M.subtype) hle

end CFSG.GorensteinWalter
