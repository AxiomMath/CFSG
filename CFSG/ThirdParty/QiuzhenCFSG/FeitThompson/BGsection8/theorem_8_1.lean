module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.theorem_7_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.theorem_7_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.proposition_7_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.theorem_7_6
import Mathlib.Order.Atoms

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

/-!
# Statements from BG Section 8

This file records the statement scaffold and formal proof infrastructure for
Theorem 8.1 from `docs/section8.tex`.
-/

section Notation

variable {G : Type*} [Group G]

/-- The set `M` of all maximal proper subgroups of `G`. -/
@[expose] public def CFSG.section8MaximalSubgroups (G : Type*) [Group G] :
    Set (Subgroup G) :=
  {M | IsCoatom M}

/-- The set `M(H)` of maximal subgroups of `G` containing `H`. -/
@[expose] public def CFSG.section8MaximalSubgroupsContaining (H : Subgroup G) :
    Set (Subgroup G) :=
  {M | M ∈ section8MaximalSubgroups G ∧ H ≤ M}

/-- A subgroup has a unique maximal overgroup in `G`. -/
@[expose] public def CFSG.section8HasUniqueMaximalOver (H : Subgroup G) : Prop :=
  ∃ M : Subgroup G, section8MaximalSubgroupsContaining H = {M}

/-- The set `U` of proper subgroups having a unique maximal overgroup. -/
@[expose] public def CFSG.section8UniqueSubgroups (G : Type*) [Group G] :
    Set (Subgroup G) :=
  {H | H ≠ ⊤ ∧ section8HasUniqueMaximalOver H}

/-- The Fitting subgroup `F(M)`, viewed as a subgroup of the ambient group. -/
public abbrev CFSG.section8FittingSubgroup (M : Subgroup G) : Subgroup G :=
  fittingSubgroupOf (G := G) M

/-- The center `Z(F(M))`, viewed as a subgroup of the ambient group. -/
public abbrev CFSG.section8CenterInFitting (M : Subgroup G) : Subgroup G :=
  centerIn (G := G) (section8FittingSubgroup M)

/-- The centralizer `C_{F(M)}(A₀)`, viewed as a subgroup of the ambient group. -/
@[expose] public def CFSG.section8CentralizerInFitting
    (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M)) : Subgroup G :=
  (Subgroup.centralizer (A₀ : Set (section8FittingSubgroup M))).map
    (section8FittingSubgroup M).subtype

/-- A subgroup of a subgroup of `G`, viewed as a subgroup of `G`. -/
@[expose] public def CFSG.section8SubgroupInAmbient {H : Subgroup G} (K : Subgroup H) :
    Subgroup G :=
  K.map H.subtype

/-- A subgroup of a Sylow subgroup of `M`, viewed as a subgroup of the ambient group. -/
@[expose] public def CFSG.section8SylowSubgroupInAmbient
    (M : Subgroup G) {p : ℕ} (P : Sylow p M) (A : Subgroup (P : Subgroup M)) :
    Subgroup G :=
  ((A.map (P : Subgroup M).subtype).map M.subtype)

/-- The Fitting subgroup `F(M)` is contained in `M`. -/
public theorem CFSG.section8FittingSubgroup_le (M : Subgroup G) :
    section8FittingSubgroup M ≤ M := by
  simpa [section8FittingSubgroup] using fittingSubgroupOf_le (G := G) M

/-- The Fitting subgroup `F(M)` is nilpotent. -/
public theorem CFSG.section8FittingSubgroup_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent (section8FittingSubgroup M) :=
  fittingSubgroupOf_isNilpotent (G := G) M

/-- The center `Z(F(M))`, viewed in `G`, is contained in `F(M)`. -/
public theorem CFSG.section8CenterInFitting_le (M : Subgroup G) :
    section8CenterInFitting M ≤ section8FittingSubgroup M := by
  exact inf_le_left

/-- The center `Z(F(M))`, viewed in `G`, is contained in `M`. -/
public theorem CFSG.section8CenterInFitting_le_maximal (M : Subgroup G) :
    section8CenterInFitting M ≤ M :=
  (section8CenterInFitting_le M).trans (section8FittingSubgroup_le M)

/-- Pulling `Z(F(M))` back to `F(M)` gives the ordinary center of `F(M)`. -/
public theorem CFSG.section8CenterInFitting_subgroupOf_eq (M : Subgroup G) :
    (section8CenterInFitting M).subgroupOf (section8FittingSubgroup M) =
      Subgroup.center (section8FittingSubgroup M) := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ section8CenterInFitting M at hx
    rcases hx with ⟨_hxF, hxCentF⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxCentF (y : G) y.property
  · intro hx
    change (x : G) ∈ section8CenterInFitting M
    refine ⟨x.property, ?_⟩
    change (x : G) ∈ Subgroup.centralizer (section8FittingSubgroup M : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)


/-- The ambient copy of `Z(F(M))` is commutative. -/
public theorem CFSG.section8CenterInFitting_isMulCommutative (M : Subgroup G) :
    IsMulCommutative (section8CenterInFitting M) := by
  refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
  apply Subtype.ext
  have hx : (x : G) ∈ section8CenterInFitting M := x.property
  rcases hx with ⟨_hxF, hxCentF⟩
  have hyF : (y : G) ∈ section8FittingSubgroup M := y.property.1
  exact (Subgroup.mem_centralizer_iff.mp hxCentF (y : G) hyF).symm

/-- The displayed containment `Z(F(M)) <= C_{F(M)}(A₀)` from Section 8. -/
public theorem CFSG.section8CenterInFitting_le_centralizerInFitting
    (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M)) :
    section8CenterInFitting M ≤ section8CentralizerInFitting M A₀ := by
  intro x hx
  rcases hx with ⟨hxF, hxCentF⟩
  refine Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a _ha
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp hxCentF (a : G) a.property

/-- The Fitting subgroup `F(M)`, pulled back to `M`, is the ordinary Fitting subgroup of `M`. -/
public theorem CFSG.section8FittingSubgroup_subgroupOf_eq (M : Subgroup G) :
    (section8FittingSubgroup M).subgroupOf M = fittingSubgroup M := by
  change ((fittingSubgroup M).map M.subtype).comap M.subtype = fittingSubgroup M
  exact
    Subgroup.comap_map_eq_self_of_injective
      (H := fittingSubgroup M) (f := M.subtype) M.subtype_injective

/-- The Fitting subgroup `F(M)` is normal inside `M`. -/
public theorem CFSG.section8FittingSubgroup_normal_in (M : Subgroup G) :
    ((section8FittingSubgroup M).subgroupOf M).Normal := by
  rw [section8FittingSubgroup_subgroupOf_eq]
  infer_instance

/-- If a prime lies in the prime support of a subgroup, that subgroup is nontrivial. -/
public theorem CFSG.section8_ne_bot_of_mem_subgroupPrimeSet
    {H : Subgroup G} {q : Nat.Primes} (hq : q ∈ subgroupPrimeSet H) :
    H ≠ ⊥ := by
  intro hH
  have hdiv : q.val ∣ Nat.card H := hq
  rw [hH] at hdiv
  exact q.2.not_dvd_one (by simpa using hdiv)

/-- A nontrivial `p`-subgroup inside `A` forces `p ∈ π(A)`. -/
public theorem CFSG.section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
    [Finite G] {A : Subgroup G} {p : Nat.Primes} {B : Subgroup A}
    (hBp : IsPGroup p.val B) (hB_ne_bot : B ≠ ⊥) :
    p ∈ subgroupPrimeSet A := by
  let : Fact p.val.Prime := ⟨p.2⟩
  obtain ⟨n, hncard⟩ := hBp.exists_card_eq
  have hBcard_ne_one : Nat.card B ≠ 1 := by
    intro hcard
    exact hB_ne_bot ((Subgroup.eq_bot_iff_card (H := B)).2 hcard)
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hBcard_ne_one
    simp [hncard, hn0]
  have hpdvdB : p.val ∣ Nat.card B := by
    rcases Nat.exists_eq_succ_of_ne_zero hn_ne_zero with ⟨m, rfl⟩
    rw [hncard, Nat.pow_succ]
    exact ⟨p.val ^ m, by simp [Nat.mul_comm]⟩
  exact dvd_trans hpdvdB (Subgroup.card_subgroup_dvd_card B)

/-- Prime support is monotone under subgroup inclusion. -/
public theorem CFSG.section8_subgroupPrimeSet_mono
    [Finite G] {H K : Subgroup G} (hHK : H ≤ K) :
    subgroupPrimeSet H ⊆ subgroupPrimeSet K := by
  intro q hqH
  have hcard_dvd : Nat.card H ∣ Nat.card K := by
    have hsub_dvd : Nat.card (H.subgroupOf K) ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card (H.subgroupOf K)
    have hcard_eq : Nat.card (H.subgroupOf K) = Nat.card H :=
      natCard_subgroupOf_eq H K hHK
    rwa [hcard_eq] at hsub_dvd
  exact dvd_trans hqH hcard_dvd

/-- A prime different from `p` is not in the prime support of a finite `p`-group. -/
public theorem CFSG.section8_not_mem_subgroupPrimeSet_of_isPGroup_ne
    [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hHp : IsPGroup p H)
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩) :
    q ∉ subgroupPrimeSet H := by
  intro hqH
  rcases hHp.exists_card_eq with ⟨n, hn⟩
  have hq_dvd_card : q.val ∣ Nat.card H := hqH
  have hq_dvd_pow : q.val ∣ p ^ n := by simpa [hn] using hq_dvd_card
  have hq_dvd_p : q.val ∣ p := q.2.dvd_of_dvd_pow hq_dvd_pow
  have hqp : q = ⟨p, Fact.out⟩ :=
    Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 (Fact.out : Nat.Prime p)).mp hq_dvd_p)
  exact hq hqp

/-- The prime support of a nontrivial finite `p`-group is exactly `{p}`. -/
public theorem CFSG.section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
    [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hHp : IsPGroup p H) (hH_ne_bot : H ≠ ⊥) :
    subgroupPrimeSet H = ({⟨p, Fact.out⟩} : Set Nat.Primes) := by
  ext q
  constructor
  · intro hqH
    by_contra hq_ne
    exact section8_not_mem_subgroupPrimeSet_of_isPGroup_ne hHp hq_ne hqH
  · intro hq
    have hqp : q = ⟨p, Fact.out⟩ := Set.mem_singleton_iff.mp hq
    subst q
    rcases hHp.exists_card_eq with ⟨n, hn⟩
    have hn0 : n ≠ 0 := by
      intro hn0
      have hcard : Nat.card H = 1 := by
        rw [hn, hn0]
        simp
      exact hH_ne_bot ((Subgroup.card_eq_one (H := H)).1 hcard)
    change p ∣ Nat.card H
    rw [hn]
    exact dvd_pow_self p hn0

/-- The generator rank of a finite group is bounded by its cardinality. -/
public theorem CFSG.section8_generatorRank_le_natCard
    (H : Type*) [Group H] [Finite H] :
    generatorRank H ≤ Nat.card H := by
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec H
  calc
    generatorRank H = Group.rank H := generatorRank_eq_group_rank H
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card H := by simpa using Finset.card_le_univ S
    _ = Nat.card H := by simp [Nat.card_eq_fintype_card]

/-- An `SCN_3` subgroup of an odd finite `p`-group is nontrivial. -/
public theorem CFSG.section8_scnSubgroups_ne_bot
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hRp : IsPGroup p R)
    {A : Subgroup R} (hA : A ∈ scnSubgroups 3 R) :
    A ≠ ⊥ := by
  have hArank : 3 ≤ generatorRank A :=
    scnSubgroup_generatorRank_at_least_three (p := p) hpodd hRp hA
  intro hAbot
  have hcard : Nat.card A = 1 := by simp [hAbot]
  have hle : generatorRank A ≤ Nat.card A := section8_generatorRank_le_natCard A
  have h31 : 3 ≤ (1 : ℕ) := by
    simpa [hcard] using hArank.trans hle
  exact (by decide : ¬ 3 ≤ (1 : ℕ)) h31

/-- The subgroup `C_{F(M)}(A₀)`, viewed in `G`, is contained in `F(M)`. -/
public theorem CFSG.section8CentralizerInFitting_le
    (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M)) :
    section8CentralizerInFitting M A₀ ≤ section8FittingSubgroup M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

/-- The prime support of `C_{F(M)}(A₀)` is contained in the prime support of `F(M)`. -/
public theorem CFSG.section8CentralizerInFitting_primeSet_subset_fitting
    [Finite G] (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M)) :
    subgroupPrimeSet (section8CentralizerInFitting M A₀) ⊆
      subgroupPrimeSet (section8FittingSubgroup M) :=
  section8_subgroupPrimeSet_mono (section8CentralizerInFitting_le M A₀)

/-- The prime support of `Z(F(M))` is contained in that of `C_{F(M)}(A₀)`. -/
public theorem CFSG.section8CenterInFitting_primeSet_subset_centralizerInFitting
    [Finite G] (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M)) :
    subgroupPrimeSet (section8CenterInFitting M) ⊆
      subgroupPrimeSet (section8CentralizerInFitting M A₀) :=
  section8_subgroupPrimeSet_mono (section8CenterInFitting_le_centralizerInFitting M A₀)

/-- A prime-support containment is the same data needed for the `IsPiSubgroup` predicate. -/
public theorem CFSG.section8_isPiSubgroup_of_subgroupPrimeSet_subset
    {H : Subgroup G} {π : Set Nat.Primes}
    (hHπ : subgroupPrimeSet H ⊆ π) :
    IsPiSubgroup (G := G) π H := by
  intro q hqH
  exact hHπ hqH


/-- Equation (8.1) reduced to the nilpotent-center prime-support equality:
if `π(Z(F(M))) = π(F(M))`, then `π(C_{F(M)}(A₀)) = π(F(M))`. -/
public theorem CFSG.section8CentralizerInFitting_primeSet_eq_fitting_of_centerInFitting_primeSet_eq
    [Finite G] (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M))
    (hZπ :
      subgroupPrimeSet (section8CenterInFitting M) =
        subgroupPrimeSet (section8FittingSubgroup M)) :
    subgroupPrimeSet (section8CentralizerInFitting M A₀) =
      subgroupPrimeSet (section8FittingSubgroup M) := by
  apply Set.Subset.antisymm
  · exact section8CentralizerInFitting_primeSet_subset_fitting M A₀
  · intro q hqF
    exact
      section8CenterInFitting_primeSet_subset_centralizerInFitting M A₀
        (by simpa [hZπ] using hqF)

/-- Pulling a subgroup back to an overgroup preserves its prime support. -/
public theorem CFSG.section8_subgroupPrimeSet_subgroupOf_eq
    {H K : Subgroup G} (hHK : H ≤ K) :
    subgroupPrimeSet (H.subgroupOf K) = subgroupPrimeSet H := by
  ext q
  change q.val ∣ Nat.card (H.subgroupOf K) ↔ q.val ∣ Nat.card H
  have hcard : Nat.card (H.subgroupOf K) = Nat.card H :=
    natCard_subgroupOf_eq H K hHK
  rw [hcard]

/-- The top subgroup of a subgroup has the same prime support as the subgroup itself. -/
public theorem CFSG.section8_subgroupPrimeSet_top_eq (K : Subgroup G) :
    subgroupPrimeSet (⊤ : Subgroup K) = subgroupPrimeSet K := by
  ext q
  change q.val ∣ Nat.card (⊤ : Subgroup K) ↔ q.val ∣ Nat.card K
  simp

/-- The center of a Sylow subgroup in a finite nilpotent group maps into the group center. -/
public theorem CFSG.section8_center_sylow_map_le_center_of_nilpotent
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {q : ℕ} [Fact q.Prime] (Q : Sylow q H) :
    (Subgroup.center (Q : Subgroup H)).map (Q : Subgroup H).subtype ≤
      Subgroup.center H := by
  classical
  have hQnorm : (Q : Subgroup H).Normal :=
    Group.IsNilpotent.sylow_normal
      (show Group.IsNilpotent H from inferInstance) q Q
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨zQ, hzQcent, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro x
  let C : Subgroup H := Subgroup.centralizer ({(zQ : H)} : Set H)
  have htop_le_C : (⊤ : Subgroup H) ≤ C := by
    rw [← Sylow.iSup_sylow_eq_top (G := H)]
    refine iSup_le ?_
    intro r
    refine iSup_le ?_
    intro hr
    have hprime : Nat.Prime r := Nat.prime_of_mem_primeFactors hr
    let : Fact r.Prime := ⟨hprime⟩
    let R : Sylow r H := default
    change (R : Subgroup H) ≤ C
    intro y hyR
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    by_cases hrq : r = q
    · subst r
      have : Unique (Sylow q H) := Sylow.unique_of_normal Q hQnorm
      have hR_eq_Q : (R : Subgroup H) = (Q : Subgroup H) := by
        exact congrArg (fun P : Sylow q H => (P : Subgroup H)) (Subsingleton.elim R Q)
      have hyQ : y ∈ (Q : Subgroup H) := by simpa [hR_eq_Q] using hyR
      have hcommQ := Subgroup.mem_center_iff.mp hzQcent ⟨y, hyQ⟩
      exact (congrArg Subtype.val hcommQ).symm
    · have hRnorm : (R : Subgroup H).Normal :=
        Group.IsNilpotent.sylow_normal
          (show Group.IsNilpotent H from inferInstance) r R
      have hdisj : Disjoint (Q : Subgroup H) (R : Subgroup H) := by
        exact
          IsPGroup.disjoint_of_ne q r (Ne.symm hrq) (Q : Subgroup H) (R : Subgroup H)
            Q.isPGroup' R.isPGroup'
      have hcomm :=
        Subgroup.commute_of_normal_of_disjoint (Q : Subgroup H) (R : Subgroup H)
          hQnorm hRnorm hdisj (zQ : H) y zQ.property hyR
      exact hcomm.eq
  have hxC : x ∈ C := htop_le_C trivial
  have hzx : (zQ : H) * x = x * (zQ : H) := by
    simpa [C, Subgroup.mem_centralizer_iff] using hxC
  exact hzx.symm

/-- In a finite nilpotent group, the center and the whole group have the same prime support. -/
public theorem CFSG.section8_subgroupPrimeSet_center_eq_top_of_nilpotent
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H] :
    subgroupPrimeSet (Subgroup.center H) = subgroupPrimeSet (⊤ : Subgroup H) := by
  classical
  apply Set.Subset.antisymm
  · exact section8_subgroupPrimeSet_mono (le_top : Subgroup.center H ≤ (⊤ : Subgroup H))
  · intro q hqtop
    let : Fact q.val.Prime := ⟨q.2⟩
    let Q : Sylow q.val H := default
    have hqH : q.val ∣ Nat.card H := by simpa [subgroupPrimeSet] using hqtop
    have hQ_ne_bot : (Q : Subgroup H) ≠ ⊥ := by
      exact Sylow.ne_bot_of_dvd_card Q hqH
    have : Nontrivial Q :=
      (Subgroup.nontrivial_iff_ne_bot (H := (Q : Subgroup H))).2 hQ_ne_bot
    have hZQ_nontrivial : Nontrivial (Subgroup.center Q) :=
      IsPGroup.center_nontrivial (p := q.val) (G := Q) Q.isPGroup'
    have hZQ_ne_bot : Subgroup.center Q ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (H := Subgroup.center Q)).1 hZQ_nontrivial
    let ZQG : Subgroup H :=
      (Subgroup.center (Q : Subgroup H)).map (Q : Subgroup H).subtype
    have hZQG_le_center : ZQG ≤ Subgroup.center H := by
      simpa [ZQG] using section8_center_sylow_map_le_center_of_nilpotent Q
    let B : Subgroup (Subgroup.center H) := ZQG.subgroupOf (Subgroup.center H)
    have hZQG_p : IsPGroup q.val ZQG := by
      have hZQ_p : IsPGroup q.val (Subgroup.center (Q : Subgroup H)) :=
        Q.isPGroup'.to_subgroup _
      exact IsPGroup.map hZQ_p (Q : Subgroup H).subtype
    have hBp : IsPGroup q.val B :=
      hZQG_p.of_equiv (Subgroup.subgroupOfEquivOfLe hZQG_le_center).symm
    have hZQG_ne_bot : ZQG ≠ ⊥ := by
      intro hbot
      have hZQ_bot : Subgroup.center (Q : Subgroup H) = ⊥ := by
        apply Subgroup.map_injective (Q : Subgroup H).subtype_injective
        simpa [ZQG] using hbot
      exact hZQ_ne_bot hZQ_bot
    have hB_ne_bot : B ≠ ⊥ := by
      intro hBbot
      have hcardB : Nat.card B = Nat.card ZQG :=
        natCard_subgroupOf_eq _ _ hZQG_le_center
      have hcardZQG : Nat.card ZQG = 1 := by
        have hcardB1 : Nat.card B = 1 := by simp [hBbot]
        exact hcardB.symm.trans hcardB1
      exact hZQG_ne_bot ((Subgroup.card_eq_one (H := ZQG)).1 hcardZQG)
    exact
      section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
        (A := Subgroup.center H) hBp hB_ne_bot

/-- Equation (8.1): `π(Z(F(M))) = π(F(M))`. -/
public theorem CFSG.section8CenterInFitting_primeSet_eq_fitting
    [Finite G] (M : Subgroup G) :
    subgroupPrimeSet (section8CenterInFitting M) =
      subgroupPrimeSet (section8FittingSubgroup M) := by
  let F : Subgroup G := section8FittingSubgroup M
  have : Group.IsNilpotent F := section8FittingSubgroup_isNilpotent M
  have hZsub :
      subgroupPrimeSet ((section8CenterInFitting M).subgroupOf F) =
        subgroupPrimeSet (⊤ : Subgroup F) := by
    rw [section8CenterInFitting_subgroupOf_eq]
    exact section8_subgroupPrimeSet_center_eq_top_of_nilpotent
  calc
    subgroupPrimeSet (section8CenterInFitting M)
        = subgroupPrimeSet ((section8CenterInFitting M).subgroupOf F) := by
          exact (section8_subgroupPrimeSet_subgroupOf_eq (section8CenterInFitting_le M)).symm
    _ = subgroupPrimeSet (⊤ : Subgroup F) := hZsub
    _ = subgroupPrimeSet F := section8_subgroupPrimeSet_top_eq F

/-- Equation (8.1): `π(C_{F(M)}(A₀)) = π(F(M))`. -/
public theorem CFSG.section8CentralizerInFitting_primeSet_eq_fitting
    [Finite G] (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M)) :
    subgroupPrimeSet (section8CentralizerInFitting M A₀) =
      subgroupPrimeSet (section8FittingSubgroup M) :=
  section8CentralizerInFitting_primeSet_eq_fitting_of_centerInFitting_primeSet_eq
    M A₀ (section8CenterInFitting_primeSet_eq_fitting M)

/-- A subgroup that is a `π`-subgroup has trivial transported `π'`-core. -/
public theorem CFSG.section8_piCoreIn_compl_eq_bot_of_isPiSubgroup
    [Finite G] {π : Set Nat.Primes} {H : Subgroup G}
    (hHπ : IsPiSubgroup (G := G) π H) :
    piCoreIn πᶜ H = ⊥ := by
  by_contra hne
  have hcard_ne_one : Nat.card (piCoreIn πᶜ H) ≠ 1 := by
    intro hcard
    exact hne ((Subgroup.card_eq_one (H := piCoreIn πᶜ H)).1 hcard)
  obtain ⟨p, hpPrime, hpDvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let p' : Nat.Primes := ⟨p, hpPrime⟩
  have hpCore : p' ∈ πᶜ :=
    piCoreIn_isPiSubgroup (G := G) πᶜ H p' hpDvd
  have hcard_dvd_H : Nat.card (piCoreIn πᶜ H) ∣ Nat.card H := by
    have hsub_dvd : Nat.card ((piCoreIn πᶜ H).subgroupOf H) ∣ Nat.card H :=
      Subgroup.card_subgroup_dvd_card ((piCoreIn πᶜ H).subgroupOf H)
    have hcard_eq :
        Nat.card ((piCoreIn πᶜ H).subgroupOf H) = Nat.card (piCoreIn πᶜ H) :=
      natCard_subgroupOf_eq (piCoreIn πᶜ H) H (piCoreIn_le (G := G) πᶜ H)
    rwa [hcard_eq] at hsub_dvd
  have hpH : p' ∈ π := hHπ p' (dvd_trans hpDvd hcard_dvd_H)
  exact hpCore hpH


/-- The subgroup `C_{F(M)}(A₀)`, viewed in `G`, is contained in `M`. -/
public theorem CFSG.section8CentralizerInFitting_le_maximal
    (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M)) :
    section8CentralizerInFitting M A₀ ≤ M :=
  (section8CentralizerInFitting_le M A₀).trans (section8FittingSubgroup_le M)

/-- The ambient copy of `A₀` lies in `C_{F(M)}(A₀)`. -/
public theorem CFSG.section8SubgroupInAmbient_le_centralizerInFitting
    {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M)) :
    section8SubgroupInAmbient A₀ ≤ section8CentralizerInFitting M A₀ := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨a, haA₀, rfl⟩
  change (a : G) ∈ section8CentralizerInFitting M A₀
  refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  apply Subtype.ext
  let : IsElementaryAbelian p A₀ := hA₀.1
  exact
    congrArg Subtype.val
      (setLike_mul_comm (s := A₀) haA₀ hb).symm

/-- The center of `C_{F(M)}(A₀)` has rank at least three when `A₀` does. -/
public theorem CFSG.section8CentralizerInFitting_center_rank_ge
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀) :
    3 ≤ groupRank (Subgroup.center (section8CentralizerInFitting M A₀)) := by
  let C : Subgroup G := section8CentralizerInFitting M A₀
  let A₀G : Subgroup G := section8SubgroupInAmbient A₀
  have hA₀G_le_C : A₀G ≤ C := by
    simpa [C, A₀G] using section8SubgroupInAmbient_le_centralizerInFitting hA₀
  let A₀C : Subgroup C := A₀G.subgroupOf C
  have hA₀C_le_center : A₀C ≤ Subgroup.center C := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    change (c : G) * (a : G) = (a : G) * (c : G)
    have hcC : (c : G) ∈ C := c.property
    have haA₀G : (a : G) ∈ A₀G := ha
    rcases Subgroup.mem_map.mp haA₀G with ⟨aF, haF_A₀, ha_eq⟩
    have hc_cent : (c : G) ∈ C := hcC
    change (c : G) ∈ section8CentralizerInFitting M A₀ at hc_cent
    rcases Subgroup.mem_map.mp hc_cent with ⟨cF, hcF_cent, hc_eq⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hcF_cent aF haF_A₀
    have hcommG : (cF : G) * (aF : G) = (aF : G) * (cF : G) :=
      congrArg Subtype.val hcomm.symm
    calc
      (c : G) * (a : G) = (cF : G) * (aF : G) := by
        simpa using congrArg₂ (fun x y : G => x * y) hc_eq.symm ha_eq.symm
      _ = (aF : G) * (cF : G) := hcommG
      _ = (a : G) * (c : G) := by
        simpa using congrArg₂ (fun x y : G => x * y) ha_eq hc_eq
  have hA₀C_p : IsPGroup p A₀C := by
    let : IsElementaryAbelian p A₀ := hA₀.1
    have hA₀p : IsPGroup p A₀ := IsElementaryAbelian.isPGroup p A₀
    have hA₀G_p : IsPGroup p A₀G :=
      IsPGroup.map hA₀p (section8FittingSubgroup M).subtype
    exact hA₀G_p.of_equiv (Subgroup.subgroupOfEquivOfLe hA₀G_le_C).symm
  have hA₀C_comm : IsMulCommutative A₀C := by
    let : IsElementaryAbelian p A₀ := hA₀.1
    have hA₀G_comm : IsMulCommutative A₀G := by
      let : IsMulCommutative A₀ := by infer_instance
      change IsMulCommutative (A₀.map (section8FittingSubgroup M).subtype)
      exact
        Subgroup.map_isMulCommutative
          (f := (section8FittingSubgroup M).subtype) (H := A₀)
    let : IsMulCommutative A₀G := hA₀G_comm
    exact Subgroup.subgroupOf_isMulCommutative (H := A₀G) (K := C)
  have hgen_eq : generatorRank A₀C = generatorRank A₀ := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    let e₁ : A₀ ≃* A₀G :=
      Subgroup.equivMapOfInjective (f := (section8FittingSubgroup M).subtype) A₀
        (section8FittingSubgroup M).subtype_injective
    let e₂ : A₀C ≃* A₀G :=
      Subgroup.subgroupOfEquivOfLe (H := A₀G) (K := C) hA₀G_le_C
    exact Group.rank_congr (e₂.trans e₁.symm)
  have hA₀C_rank : 3 ≤ generatorRank A₀C := by
    rw [hgen_eq]
    exact hA₀rank
  exact
    groupRank_at_least_three_of_generatorRank_subgroup
      (q := p) Fact.out hA₀C_le_center hA₀C_p hA₀C_comm hA₀C_rank

/-- A subgroup transported from `H` to `G` is contained in `H`. -/
public theorem CFSG.section8SubgroupInAmbient_le {H : Subgroup G} (K : Subgroup H) :
    section8SubgroupInAmbient K ≤ H := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

/-- The internal normalizer of a subgroup maps into the ambient normalizer of its
transported image. -/
public theorem CFSG.section8_normalizer_subgroupInAmbient_le
    [Finite G] {H : Subgroup G} (K : Subgroup H) :
    (Subgroup.normalizer (K : Set H)).map H.subtype ≤
      Subgroup.normalizer (section8SubgroupInAmbient K : Set G) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨h, hh, rfl⟩
  refine Subgroup.mem_normalizer_fintype ?_
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨k, hk, rfl⟩
  have hconj : h * k * h⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hh k).1 hk
  exact Subgroup.mem_map_of_mem H.subtype hconj

/-- Transporting a `p`-subgroup of `H` to `G` preserves being a `p`-subgroup. -/
public theorem CFSG.section8SubgroupInAmbient_isPGroup
    {H : Subgroup G} {p : ℕ} {K : Subgroup H} (hK : IsPGroup p K) :
    IsPGroup p (section8SubgroupInAmbient K) :=
  IsPGroup.map hK H.subtype

/-- The ambient image of a Sylow subgroup of `M` is a `p`-subgroup of `G`. -/
public theorem CFSG.section8SubgroupInAmbient_sylow_isPGroup
    {M : Subgroup G} {p : ℕ} (P : Sylow p M) :
    IsPGroup p (section8SubgroupInAmbient (P : Subgroup M)) :=
  section8SubgroupInAmbient_isPGroup P.isPGroup'

/-- The `p`-part exponent of a Sylow subgroup is the `p`-part exponent of the ambient group. -/
public theorem CFSG.section8_factorization_card_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Nat.factorization (Nat.card (P : Subgroup G)) p = Nat.factorization (Nat.card G) p := by
  rw [Sylow.card_eq_multiplicity P, Nat.factorization_pow_self Fact.out]

/-- For a finite `p`-group, the `p`-adic exponent reconstructs its cardinality. -/
public theorem CFSG.section8_card_eq_prime_pow_factorization_of_isPGroup
    [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p H) :
    Nat.card H = p ^ Nat.factorization (Nat.card H) p := by
  rcases hH.exists_card_eq with ⟨n, hn⟩
  rw [hn, Nat.factorization_pow_self Fact.out]

/-- Strict cardinal inequality between finite `p`-groups is strict inequality of their
`p`-adic exponents. -/
public theorem CFSG.section8_factorization_lt_of_isPGroup_card_lt
    [Finite G] {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hH : IsPGroup p H) (hK : IsPGroup p K) (hlt : Nat.card H < Nat.card K) :
    Nat.factorization (Nat.card H) p < Nat.factorization (Nat.card K) p := by
  have hHcard := section8_card_eq_prime_pow_factorization_of_isPGroup hH
  have hKcard := section8_card_eq_prime_pow_factorization_of_isPGroup hK
  have hpow :
      p ^ Nat.factorization (Nat.card H) p <
        p ^ Nat.factorization (Nat.card K) p := by
    rw [hHcard, hKcard] at hlt
    exact hlt
  exact (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).1 hpow

/-- A proper subgroup of a finite `p`-group has strictly smaller `p`-part than its
normalizer. -/
public theorem CFSG.section8_factorization_lt_normalizer_of_lt_top_in_pgroup
    {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    (hS : IsPGroup p S) {K : Subgroup S} (hKlt : K < ⊤) :
    Nat.factorization (Nat.card K) p <
      Nat.factorization (Nat.card (Subgroup.normalizer (K : Set S))) p := by
  have hnc : NormalizerCondition S := by
    let : Group.IsNilpotent S := IsPGroup.isNilpotent (p := p) (G := S) hS
    exact Group.normalizerCondition_of_isNilpotent (G := S)
  have hK_lt_norm : K < Subgroup.normalizer (K : Set S) := hnc K hKlt
  have hcard_lt :
      Nat.card K < Nat.card (Subgroup.normalizer (K : Set S)) :=
    natCard_lt_of_subgroup_lt hK_lt_norm
  have hKp : IsPGroup p K := hS.to_subgroup K
  have hNp : IsPGroup p (Subgroup.normalizer (K : Set S)) :=
    hS.to_subgroup (Subgroup.normalizer (K : Set S))
  exact section8_factorization_lt_of_isPGroup_card_lt hKp hNp hcard_lt

/-- A subgroup that is both a `p`-group and of order coprime to `p` is trivial. -/
public theorem CFSG.section8_eq_bot_of_isPGroup_of_coprime
    [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hHp : IsPGroup p H) (hcop : Nat.Coprime p (Nat.card H)) :
    H = ⊥ := by
  rcases hHp.exists_card_eq with ⟨n, hn⟩
  by_cases hn0 : n = 0
  · apply (Subgroup.card_eq_one (H := H)).1
    rw [hn, hn0]
    simp
  · have hpdvd : p ∣ Nat.card H := by
      rw [hn]
      exact dvd_pow_self p hn0
    have hnot : ¬ p ∣ Nat.card H :=
      (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop
    exact False.elim (hnot hpdvd)

/-- If `F(M)` is a `p`-group, then it is contained in every Sylow `p`-subgroup of `M`. -/
public theorem CFSG.section8FittingSubgroup_le_sylow
    {M : Subgroup G} {p : ℕ} (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) :
    section8FittingSubgroup M ≤ section8SubgroupInAmbient (P : Subgroup M) := by
  let F₀ : Subgroup M := (section8FittingSubgroup M).subgroupOf M
  have hF₀p : IsPGroup p F₀ := by
    have e : F₀ ≃* section8FittingSubgroup M :=
      Subgroup.subgroupOfEquivOfLe (H := section8FittingSubgroup M) (K := M)
        (section8FittingSubgroup_le M)
    exact hFp.of_equiv e.symm
  have hF₀norm : F₀.Normal := by
    simpa [F₀] using section8FittingSubgroup_normal_in (M := M)
  let : F₀.Normal := hF₀norm
  have hsup_p : IsPGroup p (F₀ ⊔ (P : Subgroup M) : Subgroup M) :=
    IsPGroup.to_sup_of_normal_left hF₀p P.isPGroup'
  have hsup_eq : F₀ ⊔ (P : Subgroup M) = (P : Subgroup M) :=
    P.is_maximal' hsup_p le_sup_right
  intro x hx
  change x ∈ (P : Subgroup M).map M.subtype
  refine Subgroup.mem_map.mpr ?_
  have hxF₀ : ⟨x, section8FittingSubgroup_le M hx⟩ ∈ F₀ := by
    exact hx
  have hxP : ⟨x, section8FittingSubgroup_le M hx⟩ ∈ (P : Subgroup M) := by
    have hxSup : ⟨x, section8FittingSubgroup_le M hx⟩ ∈ F₀ ⊔ (P : Subgroup M) :=
      (le_sup_left : F₀ ≤ F₀ ⊔ (P : Subgroup M)) hxF₀
    simpa [hsup_eq] using hxSup
  exact ⟨⟨x, section8FittingSubgroup_le M hx⟩, hxP, rfl⟩

/-- If `F(M)` is a `p`-group, then the `p'`-core of `M` is trivial. -/
public theorem CFSG.section8_pPrimeCore_eq_bot_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hFp : IsPGroup p (section8FittingSubgroup M)) :
    pPrimeCore p M = ⊥ := by
  have : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  rw [pPrimeCore_eq_bot_iff]
  intro K hKnorm hKcop
  by_contra hKne
  have hfitK_ne_bot : fittingSubgroup K ≠ ⊥ := by
    intro hfitK
    have hcardK : Nat.card K = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable K).mp hfitK
    exact hKne ((Subgroup.card_eq_one (H := K)).1 hcardK)
  let L : Subgroup M := (fittingSubgroup K).map K.subtype
  have hL_ne_bot : L ≠ ⊥ := by
    intro hLbot
    exact hfitK_ne_bot
      (Subgroup.map_injective K.subtype_injective (by simpa [L] using hLbot))
  have hL_norm : L.Normal := by
    let : K.Normal := hKnorm
    let : (fittingSubgroup K).Characteristic := fittingSubgroup_characteristic
    change ((fittingSubgroup K).map K.subtype).Normal
    infer_instance
  have hL_nil : Group.IsNilpotent L := by
    have : Group.IsNilpotent (fittingSubgroup K) := by infer_instance
    let e : fittingSubgroup K ≃* L :=
      Subgroup.equivMapOfInjective (f := K.subtype) (fittingSubgroup K) K.subtype_injective
    exact Group.nilpotent_of_mulEquiv (G := fittingSubgroup K) (G' := L) e
  have hL_le_fitM : L ≤ fittingSubgroup M :=
    le_sSup ⟨hL_norm, hL_nil⟩
  have hfitM_p : IsPGroup p (fittingSubgroup M) := by
    have e : fittingSubgroup M ≃* section8FittingSubgroup M := by
      refine MulEquiv.trans ?_
        (Subgroup.subgroupOfEquivOfLe
          (H := section8FittingSubgroup M) (K := M) (section8FittingSubgroup_le M))
      exact MulEquiv.subgroupCongr (section8FittingSubgroup_subgroupOf_eq M).symm
    exact hFp.of_equiv e.symm
  have hL_p : IsPGroup p L := by
    let Lsub : Subgroup (fittingSubgroup M) := L.subgroupOf (fittingSubgroup M)
    have hLsub_p : IsPGroup p Lsub := hfitM_p.to_subgroup Lsub
    have e : Lsub ≃* L :=
      Subgroup.subgroupOfEquivOfLe (H := L) (K := fittingSubgroup M) hL_le_fitM
    exact hLsub_p.of_equiv e
  have hLcop : Nat.Coprime p (Nat.card L) := by
    have hL_dvd_fitK : Nat.card L ∣ Nat.card (fittingSubgroup K) := by
      simpa [L] using Subgroup.card_map_dvd (H := fittingSubgroup K) K.subtype
    have hfitK_dvd_K : Nat.card (fittingSubgroup K) ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card (fittingSubgroup K)
    exact Nat.Coprime.of_dvd_right (dvd_trans hL_dvd_fitK hfitK_dvd_K) hKcop
  exact hL_ne_bot (section8_eq_bot_of_isPGroup_of_coprime hL_p hLcop)

/-- If `F(M)` is a `p`-group, then `O_{p',p}(M)` is the ordinary Fitting subgroup of `M`. -/
public theorem CFSG.section8_Op_p'p_eq_fittingSubgroup_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hFp : IsPGroup p (section8FittingSubgroup M)) :
    Op_p'p p M = fittingSubgroup M := by
  have hcore : pPrimeCore p M = ⊥ :=
    section8_pPrimeCore_eq_bot_of_fitting_isPGroup hM hFp
  calc
    Op_p'p p M = pCore p M :=
      Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := M) (p := p) hcore
    _ = fittingSubgroup M := (Fitting_eq_pcore M p hcore).symm

/-- In part (b), Theorem 6.1 puts every transported `SCN_3(P)` subgroup inside `F(M)`. -/
public theorem CFSG.section8SylowSubgroupInAmbient_le_fitting_of_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    section8SylowSubgroupInAmbient M P A ≤ section8FittingSubgroup M := by
  have : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hAcomm : IsMulCommutative A :=
    (scnSubgroup_normal_commutative
      (p := p) (R := (P : Subgroup M)) P.isPGroup' hA).2
  let : A.Normal := hA.1
  let : IsMulCommutative A := hAcomm
  have hA_le_op : A.map (P : Subgroup M).subtype ≤ Op_p'p p M :=
    theorem_6_1 (G := M) (p := p) hModd P A
  have hop_eq : Op_p'p p M = fittingSubgroup M :=
    section8_Op_p'p_eq_fittingSubgroup_of_fitting_isPGroup hM hFp
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hy_fitM : y ∈ fittingSubgroup M := by
    simpa [hop_eq] using hA_le_op hy
  have hy_Fsub : y ∈ (section8FittingSubgroup M).subgroupOf M := by
    simpa [section8FittingSubgroup_subgroupOf_eq M] using hy_fitM
  exact hy_Fsub

/-- Transporting a subgroup of `H` to `G` and then pulling back to `H` recovers it. -/
public theorem CFSG.section8SubgroupInAmbient_subgroupOf_eq {H : Subgroup G} (K : Subgroup H) :
    (section8SubgroupInAmbient K).subgroupOf H = K := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ K.map H.subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hy_eq : y = x := Subtype.ext hyx
    simpa [hy_eq] using hy
  · intro hx
    change (x : G) ∈ K.map H.subtype
    exact Subgroup.mem_map_of_mem H.subtype hx

/-- Transporting a subgroup to the ambient group is trivial exactly when the original subgroup is. -/
public theorem CFSG.section8SubgroupInAmbient_eq_bot_iff {H : Subgroup G} (K : Subgroup H) :
    section8SubgroupInAmbient K = ⊥ ↔ K = ⊥ := by
  constructor
  · intro hK
    apply Subgroup.map_injective H.subtype_injective
    simpa [section8SubgroupInAmbient] using hK
  · intro hK
    rw [hK]
    simp [section8SubgroupInAmbient]

/-- A subgroup with generator rank at least three is nontrivial. -/
public theorem CFSG.section8_ne_bot_of_three_le_generatorRank
    (H : Type*) [Group H] [Finite H] {A : Subgroup H}
    (hArank : 3 ≤ generatorRank A) :
    A ≠ ⊥ := by
  intro hAbot
  have hcard : Nat.card A = 1 := by simp [hAbot]
  have hle : generatorRank A ≤ Nat.card A := section8_generatorRank_le_natCard A
  have h31 : 3 ≤ (1 : ℕ) := by
    simpa [hcard] using hArank.trans hle
  exact (by decide : ¬ 3 ≤ (1 : ℕ)) h31

/-- The centralizer `C_{F(M)}(A₀)` is nontrivial under the rank hypothesis on `A₀`. -/
public theorem CFSG.section8CentralizerInFitting_ne_bot_of_rank
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀) :
    section8CentralizerInFitting M A₀ ≠ ⊥ := by
  have hA₀_ne_bot : A₀ ≠ ⊥ :=
    section8_ne_bot_of_three_le_generatorRank (section8FittingSubgroup M) hA₀rank
  intro hCbot
  have hA₀G_bot : section8SubgroupInAmbient A₀ = (⊥ : Subgroup G) := by
    apply le_bot_iff.mp
    simpa [hCbot] using section8SubgroupInAmbient_le_centralizerInFitting hA₀
  exact hA₀_ne_bot ((section8SubgroupInAmbient_eq_bot_iff A₀).1 hA₀G_bot)

/-- A transported normal subgroup is normal inside the containing subgroup. -/
public theorem CFSG.section8SubgroupInAmbient_normal_in
    {H : Subgroup G} {K : Subgroup H} (hK : K.Normal) :
    ((section8SubgroupInAmbient K).subgroupOf H).Normal := by
  rw [section8SubgroupInAmbient_subgroupOf_eq]
  exact hK

/-- The Thompson subgroup is contained in the subgroup from which it is built. -/
public theorem CFSG.section8_thompsonSubgroup_le (S : Subgroup G) :
    thompsonSubgroup S ≤ S := by
  change sSup (thompsonAbelianSubgroups (G := G) S) ≤ S
  exact sSup_le (by intro A hA; exact hA.1)

/-- Computing the Thompson subgroup inside a subgroup and mapping it back to the ambient group
recovers the ambient Thompson subgroup. -/
public theorem CFSG.section8_thompsonSubgroup_top_map_subtype (S : Subgroup G) :
    (thompsonSubgroup (⊤ : Subgroup S)).map S.subtype = thompsonSubgroup S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    change sSup (thompsonAbelianSubgroups (G := S) (⊤ : Subgroup S)) ≤
      (thompsonSubgroup S).comap S.subtype
    apply sSup_le
    intro A hA
    change A ≤ (thompsonSubgroup S).comap S.subtype
    rw [← Subgroup.map_le_iff_le_comap]
    apply le_sSup
    rcases hA with ⟨_hA_top, hAcomm, hAmax⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    · exact Subgroup.map_isMulCommutative (f := S.subtype) (H := A)
    · intro B hBS hBcomm
      let Bsub : Subgroup S := B.subgroupOf S
      have hBsub_comm : IsMulCommutative Bsub := by
        refine { is_comm := ⟨fun a b => ?_⟩ }
        apply Subtype.ext
        apply Subtype.ext
        exact setLike_mul_comm (s := B) a.property b.property
      have hcard_Bsub_le_A : Nat.card Bsub ≤ Nat.card A :=
        hAmax Bsub le_top hBsub_comm
      have hcard_B_eq_Bsub : Nat.card B = Nat.card Bsub := by
        exact
          (Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := B) (K := S) hBS).toEquiv).symm
      have hcard_Amap_eq_A : Nat.card (A.map S.subtype) = Nat.card A := by
        exact Subgroup.card_map_of_injective (K := A) (f := S.subtype) S.subtype_injective
      rw [hcard_Amap_eq_A]
      simpa [hcard_B_eq_Bsub] using hcard_Bsub_le_A
  · change sSup (thompsonAbelianSubgroups (G := G) S) ≤
      (thompsonSubgroup (⊤ : Subgroup S)).map S.subtype
    apply sSup_le
    intro B hB
    rcases hB with ⟨hBS, hBcomm, hBmax⟩
    let Bsub : Subgroup S := B.subgroupOf S
    have hBsub_mem : Bsub ∈ thompsonAbelianSubgroups (⊤ : Subgroup S) := by
      refine ⟨le_top, ?_, ?_⟩
      · refine { is_comm := ⟨fun a b => ?_⟩ }
        apply Subtype.ext
        apply Subtype.ext
        exact setLike_mul_comm (s := B) a.property b.property
      · intro A _hA_top hAcomm
        have hAmap_le_S : A.map S.subtype ≤ S := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
          exact y.property
        have hAmap_comm : IsMulCommutative (A.map S.subtype) :=
          Subgroup.map_isMulCommutative (f := S.subtype) (H := A)
        have hcard_Amap_le_B : Nat.card (A.map S.subtype) ≤ Nat.card B :=
          hBmax (A.map S.subtype) hAmap_le_S hAmap_comm
        have hcard_Amap_eq_A : Nat.card (A.map S.subtype) = Nat.card A := by
          exact
            Subgroup.card_map_of_injective (K := A) (f := S.subtype) S.subtype_injective
        have hcard_B_eq_Bsub : Nat.card B = Nat.card Bsub := by
          exact
            (Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (H := B) (K := S) hBS).toEquiv).symm
        rw [← hcard_Amap_eq_A]
        simpa [hcard_B_eq_Bsub] using hcard_Amap_le_B
    have hBsub_le_J : Bsub ≤ thompsonSubgroup (⊤ : Subgroup S) := le_sSup hBsub_mem
    intro x hxB
    have hxmap : x ∈ Bsub.map S.subtype := by
      change x ∈ (B.subgroupOf S).map S.subtype
      rw [Subgroup.subgroupOf_map_subtype]
      exact ⟨hxB, hBS hxB⟩
    exact Subgroup.map_mono hBsub_le_J hxmap

/-- The Thompson subgroup of the top subgroup is preserved by multiplicative equivalence. -/
public theorem CFSG.section8_thompsonSubgroup_top_map_equiv
    {G' : Type*} [Group G'] (e : G ≃* G') :
    (thompsonSubgroup (⊤ : Subgroup G)).map e.toMonoidHom =
      thompsonSubgroup (⊤ : Subgroup G') := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    change sSup (thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G)) ≤
      (thompsonSubgroup (⊤ : Subgroup G')).comap e.toMonoidHom
    apply sSup_le
    intro A hA
    change A ≤ (thompsonSubgroup (⊤ : Subgroup G')).comap e.toMonoidHom
    rw [← Subgroup.map_le_iff_le_comap]
    apply le_sSup
    rcases hA with ⟨_hA_top, hAcomm, hAmax⟩
    refine ⟨le_top, ?_, ?_⟩
    · exact Subgroup.map_isMulCommutative (f := e.toMonoidHom) (H := A)
    · intro B _hB_top _hBcomm
      have hBpre_comm : IsMulCommutative (B.map e.symm.toMonoidHom) :=
        Subgroup.map_isMulCommutative (f := e.symm.toMonoidHom) (H := B)
      have hcard_Bpre_le_A : Nat.card (B.map e.symm.toMonoidHom) ≤ Nat.card A :=
        hAmax (B.map e.symm.toMonoidHom) le_top hBpre_comm
      have hcard_Bpre_eq_B : Nat.card (B.map e.symm.toMonoidHom) = Nat.card B :=
        Subgroup.card_map_of_injective (K := B) (f := e.symm.toMonoidHom) e.symm.injective
      have hcard_Amap_eq_A : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
        Subgroup.card_map_of_injective (K := A) (f := e.toMonoidHom) e.injective
      rw [hcard_Bpre_eq_B] at hcard_Bpre_le_A
      rwa [hcard_Amap_eq_A]
  · change sSup (thompsonAbelianSubgroups (G := G') (⊤ : Subgroup G')) ≤
      (thompsonSubgroup (⊤ : Subgroup G)).map e.toMonoidHom
    apply sSup_le
    intro B hB x hxB
    have hBpre_mem : B.map e.symm.toMonoidHom ∈
        thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G) := by
      rcases hB with ⟨_hB_top, _hBcomm, hBmax⟩
      refine ⟨le_top, ?_, ?_⟩
      · exact Subgroup.map_isMulCommutative (f := e.symm.toMonoidHom) (H := B)
      · intro A _hA_top _hAcomm
        have hAmap_comm : IsMulCommutative (A.map e.toMonoidHom) :=
          Subgroup.map_isMulCommutative (f := e.toMonoidHom) (H := A)
        have hcard_Amap_le_B : Nat.card (A.map e.toMonoidHom) ≤ Nat.card B :=
          hBmax (A.map e.toMonoidHom) le_top hAmap_comm
        have hcard_Amap_eq_A : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
          Subgroup.card_map_of_injective (K := A) (f := e.toMonoidHom) e.injective
        have hcard_Bpre_eq_B : Nat.card (B.map e.symm.toMonoidHom) = Nat.card B :=
          Subgroup.card_map_of_injective (K := B) (f := e.symm.toMonoidHom) e.symm.injective
        rw [hcard_Amap_eq_A] at hcard_Amap_le_B
        rw [← hcard_Bpre_eq_B] at hcard_Amap_le_B
        exact hcard_Amap_le_B
    have hxpre : e.symm x ∈ B.map e.symm.toMonoidHom :=
      Subgroup.mem_map_of_mem e.symm.toMonoidHom hxB
    have hxJ : e.symm x ∈ thompsonSubgroup (⊤ : Subgroup G) :=
      le_sSup hBpre_mem hxpre
    have hxmap : e (e.symm x) ∈ (thompsonSubgroup (⊤ : Subgroup G)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hxJ
    simpa using hxmap

/-- The center of the top Thompson subgroup is preserved by multiplicative equivalence. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_top_map_equiv
    {G' : Type*} [Group G'] (e : G ≃* G') :
    (centerIn (thompsonSubgroup (⊤ : Subgroup G))).map e.toMonoidHom =
      centerIn (thompsonSubgroup (⊤ : Subgroup G')) := by
  let J : Subgroup G := thompsonSubgroup (⊤ : Subgroup G)
  let J' : Subgroup G' := thompsonSubgroup (⊤ : Subgroup G')
  have hJmap : J.map e.toMonoidHom = J' := by
    simpa [J, J'] using section8_thompsonSubgroup_top_map_equiv e
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyZ, rfl⟩
    change y ∈ centerIn J at hyZ
    change e y ∈ centerIn J'
    rcases hyZ with ⟨hyJ, hyCent⟩
    refine ⟨?_, ?_⟩
    · have hmem : e y ∈ J.map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hyJ
      rw [hJmap] at hmem
      exact hmem
    · change e y ∈ Subgroup.centralizer (J' : Set G')
      rw [Subgroup.mem_centralizer_iff]
      intro z hzJ'
      have hzMap : z ∈ J.map e.toMonoidHom := by
        rw [hJmap]
        exact hzJ'
      rcases Subgroup.mem_map.mp hzMap with ⟨w, hwJ, hwz⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hyCent w hwJ
      rw [← hwz]
      simpa using congrArg e hcomm
  · intro x hx
    change x ∈ centerIn J' at hx
    change x ∈ (centerIn J).map e.toMonoidHom
    have hxpre : e.symm x ∈ centerIn J := by
      rcases hx with ⟨hxJ', hxCent'⟩
      refine ⟨?_, ?_⟩
      · have hxMap : x ∈ J.map e.toMonoidHom := by
          rw [hJmap]
          exact hxJ'
        rcases Subgroup.mem_map.mp hxMap with ⟨y, hyJ, hyx⟩
        have hy_eq : y = e.symm x := by
          apply e.injective
          simpa [hyx]
        simpa [hy_eq] using hyJ
      · change e.symm x ∈ Subgroup.centralizer (J : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hyJ
        have hyJ' : e y ∈ J' := by
          have hmem : e y ∈ J.map e.toMonoidHom :=
            Subgroup.mem_map_of_mem e.toMonoidHom hyJ
          rw [hJmap] at hmem
          exact hmem
        have hcomm' := Subgroup.mem_centralizer_iff.mp hxCent' (e y) hyJ'
        apply e.injective
        simpa using hcomm'
    have hxmap : e (e.symm x) ∈ (centerIn J).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hxpre
    simpa using hxmap

/-- The Thompson subgroup of the whole ambient group is characteristic. -/
public theorem CFSG.section8_thompsonSubgroup_top_characteristic :
    (thompsonSubgroup (⊤ : Subgroup G)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_le_iff_le_comap]
  change sSup (thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G)) ≤
    (thompsonSubgroup (⊤ : Subgroup G)).comap φ.toMonoidHom
  apply sSup_le
  intro A hA
  change A ≤ (thompsonSubgroup (⊤ : Subgroup G)).comap φ.toMonoidHom
  rw [← Subgroup.map_le_iff_le_comap]
  apply le_sSup
  rcases hA with ⟨_hA_top, hAcomm, hAmax⟩
  refine ⟨le_top, ?_, ?_⟩
  · exact Subgroup.map_isMulCommutative (f := φ.toMonoidHom) (H := A)
  · intro B _hB_top hBcomm
    have hBpre_comm : IsMulCommutative (B.map φ.symm.toMonoidHom) :=
      Subgroup.map_isMulCommutative (f := φ.symm.toMonoidHom) (H := B)
    have hcard_Bpre_le_A : Nat.card (B.map φ.symm.toMonoidHom) ≤ Nat.card A :=
      hAmax (B.map φ.symm.toMonoidHom) le_top hBpre_comm
    have hcard_Bpre_eq_B : Nat.card (B.map φ.symm.toMonoidHom) = Nat.card B := by
      exact
        Subgroup.card_map_of_injective (K := B) (f := φ.symm.toMonoidHom)
          φ.symm.injective
    have hcard_Amap_eq_A : Nat.card (A.map φ.toMonoidHom) = Nat.card A := by
      exact Subgroup.card_map_of_injective (K := A) (f := φ.toMonoidHom) φ.injective
    rw [hcard_Bpre_eq_B] at hcard_Bpre_le_A
    rwa [hcard_Amap_eq_A]

/-- Pulling `J(S)` back to `S` gives the Thompson subgroup of the top subgroup of `S`. -/
public theorem CFSG.section8_thompsonSubgroup_subgroupOf_eq_top (S : Subgroup G) :
    (thompsonSubgroup S).subgroupOf S = thompsonSubgroup (⊤ : Subgroup S) := by
  apply Subgroup.map_injective S.subtype_injective
  calc
    ((thompsonSubgroup S).subgroupOf S).map S.subtype =
        thompsonSubgroup S := by
          rw [Subgroup.subgroupOf_map_subtype]
          exact inf_eq_left.2 (section8_thompsonSubgroup_le S)
    _ = (thompsonSubgroup (⊤ : Subgroup S)).map S.subtype :=
        (section8_thompsonSubgroup_top_map_subtype S).symm

/-- `J(S)`, regarded as a subgroup of `S`, is characteristic in `S`. -/
public theorem CFSG.section8_thompsonSubgroup_subgroupOf_characteristic (S : Subgroup G) :
    ((thompsonSubgroup S).subgroupOf S).Characteristic := by
  rw [section8_thompsonSubgroup_subgroupOf_eq_top S]
  exact section8_thompsonSubgroup_top_characteristic

/-- The pullback of `Z(J(S))` to `S` is the center of the pulled-back Thompson subgroup. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_subgroupOf_eq (S : Subgroup G) :
    (centerIn (thompsonSubgroup S)).subgroupOf S =
      (Subgroup.center ((thompsonSubgroup S).subgroupOf S)).map
        ((thompsonSubgroup S).subgroupOf S).subtype := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ centerIn (thompsonSubgroup S) at hx
    rcases hx with ⟨hxJ, hxCent⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxJ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxCent (y : G) y.property
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyCenter, hyx⟩
    have hyxG : (((y : (thompsonSubgroup S).subgroupOf S) : S) : G) = (x : G) :=
      congrArg Subtype.val hyx
    change (x : G) ∈ centerIn (thompsonSubgroup S)
    refine ⟨?_, ?_⟩
    · have hyJ :
          ((y : (thompsonSubgroup S).subgroupOf S) : S) ∈
            (thompsonSubgroup S).subgroupOf S := y.property
      have hyJg :
          (((y : (thompsonSubgroup S).subgroupOf S) : S) : G) ∈
            thompsonSubgroup S := hyJ
      simpa [hyxG] using hyJg
    · change (x : G) ∈ Subgroup.centralizer (thompsonSubgroup S : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hzJ
      let zS : S := ⟨z, section8_thompsonSubgroup_le S hzJ⟩
      let zJ : (thompsonSubgroup S).subgroupOf S := ⟨zS, hzJ⟩
      have hcomm := Subgroup.mem_center_iff.mp hyCenter zJ
      have hcommG :
          z * (((y : (thompsonSubgroup S).subgroupOf S) : S) : G) =
            (((y : (thompsonSubgroup S).subgroupOf S) : S) : G) * z := by
        simpa [zJ, zS] using congrArg Subtype.val (congrArg Subtype.val hcomm)
      simpa [hyxG] using hcommG

/-- Pulling `Z(J(S))` back to `S` is the center of the Thompson subgroup computed
internally in `S`. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_subgroupOf_eq_top (S : Subgroup G) :
    (centerIn (thompsonSubgroup S)).subgroupOf S =
      centerIn (thompsonSubgroup (⊤ : Subgroup S)) := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ centerIn (thompsonSubgroup S) at hx
    rcases hx with ⟨hxJ, hxCent⟩
    refine ⟨?_, ?_⟩
    · have hxJsub : x ∈ (thompsonSubgroup S).subgroupOf S := hxJ
      simpa [section8_thompsonSubgroup_subgroupOf_eq_top (S := S)] using hxJsub
    · change x ∈ Subgroup.centralizer (thompsonSubgroup (⊤ : Subgroup S) : Set S)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyJ
      apply Subtype.ext
      have hyJsub : y ∈ (thompsonSubgroup S).subgroupOf S := by
        simpa [section8_thompsonSubgroup_subgroupOf_eq_top (S := S)] using hyJ
      exact Subgroup.mem_centralizer_iff.mp hxCent (y : G) hyJsub
  · intro hx
    change x ∈ centerIn (thompsonSubgroup (⊤ : Subgroup S)) at hx
    change (x : G) ∈ centerIn (thompsonSubgroup S)
    rcases hx with ⟨hxJ, hxCent⟩
    refine ⟨?_, ?_⟩
    · have hxJsub : x ∈ (thompsonSubgroup S).subgroupOf S := by
        simpa [section8_thompsonSubgroup_subgroupOf_eq_top (S := S)] using hxJ
      exact hxJsub
    · change (x : G) ∈ Subgroup.centralizer (thompsonSubgroup S : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyJ
      have hyS : y ∈ S := section8_thompsonSubgroup_le S hyJ
      let yS : S := ⟨y, hyS⟩
      have hyJtop : yS ∈ thompsonSubgroup (⊤ : Subgroup S) := by
        have hyJsub : yS ∈ (thompsonSubgroup S).subgroupOf S := by
          exact hyJ
        simpa [section8_thompsonSubgroup_subgroupOf_eq_top (S := S)] using hyJsub
      have hcomm := Subgroup.mem_centralizer_iff.mp hxCent yS hyJtop
      exact congrArg Subtype.val hcomm

/-- `Z(J(S))`, regarded as a subgroup of `S`, is characteristic in `S`. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_subgroupOf_characteristic (S : Subgroup G) :
    ((centerIn (thompsonSubgroup S)).subgroupOf S).Characteristic := by
  rw [section8_centerIn_thompsonSubgroup_subgroupOf_eq S]
  let : ((thompsonSubgroup S).subgroupOf S).Characteristic :=
    section8_thompsonSubgroup_subgroupOf_characteristic S
  exact
    characteristic_map_subtype_of_characteristic
      ((thompsonSubgroup S).subgroupOf S) (Subgroup.center ((thompsonSubgroup S).subgroupOf S))

/-- A characteristic subgroup remains characteristic after transport by a group isomorphism. -/
public theorem CFSG.section8_characteristic_map_equiv
    {G' : Type*} [Group G'] (K : Subgroup G) [K.Characteristic] (e : G ≃* G') :
    (K.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hyKe, rfl⟩
  rcases Subgroup.mem_map.mp hyKe with ⟨z, hzK, rfl⟩
  let ψ : G ≃* G := (e.trans φ).trans e.symm
  have hψK : K.map ψ.toMonoidHom ≤ K :=
    (Subgroup.characteristic_iff_map_le.mp (inferInstance : K.Characteristic)) ψ
  have hψz : ψ z ∈ K := hψK (Subgroup.mem_map_of_mem ψ.toMonoidHom hzK)
  exact Subgroup.mem_map.mpr ⟨ψ z, hψz, by simp [ψ]⟩

/-- A nontrivial subgroup has a nontrivial member of its Thompson family. -/
public theorem CFSG.section8_exists_nontrivial_thompsonAbelianSubgroup_of_ne_bot
    [Finite G] {S : Subgroup G} (hS_ne_bot : S ≠ ⊥) :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups S ∧ A ≠ ⊥ := by
  classical
  have hx_exists : ∃ x : G, x ∈ S ∧ x ≠ 1 := by
    by_contra hnone
    apply hS_ne_bot
    ext x
    constructor
    · intro hxS
      have hx1 : x = 1 := by
        by_contra hxne
        exact hnone ⟨x, hxS, hxne⟩
      rw [hx1]
      exact Subgroup.one_mem ⊥
    · intro hxbot
      have hx1 : x = 1 := by simpa using hxbot
      rw [hx1]
      exact S.one_mem
  rcases hx_exists with ⟨x, hxS, hxne⟩
  let C : Set (Subgroup G) := {A | A ≤ S ∧ IsMulCommutative A}
  have hCfinite : C.Finite := Set.toFinite C
  have hImageFinite : ((fun B : Subgroup G => Nat.card B) '' C).Finite :=
    hCfinite.image _
  have hzpow_mem : Subgroup.zpowers x ∈ C := by
    exact ⟨(Subgroup.zpowers_le).2 hxS, inferInstance⟩
  have hCnonempty : C.Nonempty := ⟨Subgroup.zpowers x, hzpow_mem⟩
  obtain ⟨A, hAmax⟩ :=
    hImageFinite.exists_maximalFor' (f := fun B : Subgroup G => Nat.card B) C hCnonempty
  refine ⟨A, ?_, ?_⟩
  · rcases hAmax.1 with ⟨hAS, hAcomm⟩
    exact ⟨hAS, hAcomm, fun B hBS hBcomm => hAmax.le ⟨hBS, hBcomm⟩⟩
  · intro hAbot
    have hzpow_card_le : Nat.card (Subgroup.zpowers x) ≤ 1 := by
      simpa [hAbot] using hAmax.le hzpow_mem
    have hzpow_card_eq : Nat.card (Subgroup.zpowers x) = 1 :=
      le_antisymm hzpow_card_le (Nat.card_pos (α := Subgroup.zpowers x))
    have hzpow_bot : Subgroup.zpowers x = ⊥ :=
      (Subgroup.card_eq_one (H := Subgroup.zpowers x)).1 hzpow_card_eq
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hzpow_bot] using (Subgroup.mem_zpowers x)
    exact hxne (by simpa using hxbot)

/-- The Thompson subgroup of a nontrivial subgroup is nontrivial. -/
public theorem CFSG.section8_thompsonSubgroup_ne_bot_of_ne_bot
    [Finite G] {S : Subgroup G} (hS_ne_bot : S ≠ ⊥) :
    thompsonSubgroup S ≠ ⊥ := by
  rcases section8_exists_nontrivial_thompsonAbelianSubgroup_of_ne_bot hS_ne_bot with
    ⟨A, hA, hA_ne_bot⟩
  intro hJbot
  have hA_le_J : A ≤ thompsonSubgroup S := le_sSup hA
  exact hA_ne_bot (le_bot_iff.mp (by simpa [hJbot] using hA_le_J))

/-- The center-in-ambient of a nontrivial finite `p`-subgroup is nontrivial. -/
public theorem CFSG.section8_centerIn_ne_bot_of_isPGroup
    [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hHp : IsPGroup p H) (hH_ne_bot : H ≠ ⊥) :
    centerIn H ≠ ⊥ := by
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hH_ne_bot
  have hcenter_nontrivial : Nontrivial (Subgroup.center H) :=
    IsPGroup.center_nontrivial (p := p) (G := H) hHp
  have hcenter_ne_bot : Subgroup.center H ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (H := Subgroup.center H)).1 hcenter_nontrivial
  intro hcenterIn_bot
  have hcenter_map_bot : (Subgroup.center H).map H.subtype = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxCenterIn : x ∈ centerIn H := by
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      refine ⟨z.property, ?_⟩
      change (z : G) ∈ Subgroup.centralizer (H : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
    simpa [hcenterIn_bot] using hxCenterIn
  have hcenter_bot : Subgroup.center H = ⊥ := by
    apply Subgroup.map_injective H.subtype_injective
    simpa using hcenter_map_bot
  exact hcenter_ne_bot hcenter_bot

/-- If a finite `p`-subgroup is nontrivial, then `Z(J(S))` is nontrivial. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot
    [Finite G] {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    (hSp : IsPGroup p S) (hS_ne_bot : S ≠ ⊥) :
    centerIn (thompsonSubgroup S) ≠ ⊥ := by
  have hJ_le_S : thompsonSubgroup S ≤ S := section8_thompsonSubgroup_le S
  have hJ_ne_bot : thompsonSubgroup S ≠ ⊥ :=
    section8_thompsonSubgroup_ne_bot_of_ne_bot hS_ne_bot
  let Jsub : Subgroup S := (thompsonSubgroup S).subgroupOf S
  have hJsub_p : IsPGroup p Jsub := hSp.to_subgroup Jsub
  have e : Jsub ≃* thompsonSubgroup S :=
    Subgroup.subgroupOfEquivOfLe (H := thompsonSubgroup S) (K := S) hJ_le_S
  have hJp : IsPGroup p (thompsonSubgroup S) := hJsub_p.of_equiv e
  exact section8_centerIn_ne_bot_of_isPGroup hJp hJ_ne_bot

/-- In branch (b), the Sylow subgroup of `M` is nontrivial. -/
public theorem CFSG.section8_sylow_ne_bot_of_mem_fitting_primeSet_of_fitting_isPGroup
    {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M)) (P : Sylow p M) :
    (P : Subgroup M) ≠ ⊥ := by
  intro hPbot
  have hPambient_bot : section8SubgroupInAmbient (P : Subgroup M) = ⊥ := by
    rw [hPbot]
    simp [section8SubgroupInAmbient]
  have hF_le_bot : section8FittingSubgroup M ≤ (⊥ : Subgroup G) := by
    simpa [hPambient_bot] using section8FittingSubgroup_le_sylow hFp P
  exact (section8_ne_bot_of_mem_subgroupPrimeSet hpF) (le_bot_iff.mp hF_le_bot)

/-- In part (b), Theorem 6.2 makes `Z(J(P))` normal in `M` once `F(M)` is a `p`-group. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_normal_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) :
    (centerIn (thompsonSubgroup P) : Subgroup M).Normal := by
  have : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hcore : pPrimeCore p M = ⊥ :=
    section8_pPrimeCore_eq_bot_of_fitting_isPGroup hM hFp
  have hnorm : (centerIn (thompsonSubgroup P) ⊔ pPrimeCore p M : Subgroup M).Normal :=
    theorem_6_2 (G := M) hModd P
  simpa [hcore] using hnorm

/-- A subgroup transported from a Sylow subgroup of `M` to `G` is contained in `M`. -/
public theorem CFSG.section8SylowSubgroupInAmbient_le
    (M : Subgroup G) {p : ℕ} (P : Sylow p M) (A : Subgroup (P : Subgroup M)) :
    section8SylowSubgroupInAmbient M P A ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

/-- Transporting a subgroup of a Sylow subgroup to `G` preserves being a `p`-subgroup. -/
public theorem CFSG.section8SylowSubgroupInAmbient_isPGroup
    (M : Subgroup G) {p : ℕ} (P : Sylow p M) (A : Subgroup (P : Subgroup M)) :
    IsPGroup p (section8SylowSubgroupInAmbient M P A) := by
  have hA_M : IsPGroup p (A.map (P : Subgroup M).subtype) :=
    IsPGroup.map (P.isPGroup'.to_subgroup A) (P : Subgroup M).subtype
  exact IsPGroup.map hA_M M.subtype

/-- Pulling a transported subgroup of a Sylow subgroup back to `M` gives its image in `M`. -/
public theorem CFSG.section8SylowSubgroupInAmbient_subgroupOf_eq
    (M : Subgroup G) {p : ℕ} (P : Sylow p M) (A : Subgroup (P : Subgroup M)) :
    (section8SylowSubgroupInAmbient M P A).subgroupOf M =
      A.map (P : Subgroup M).subtype := by
  change
    (((A.map (P : Subgroup M).subtype).map M.subtype).comap M.subtype =
      A.map (P : Subgroup M).subtype)
  exact
    Subgroup.comap_map_eq_self_of_injective
      (H := A.map (P : Subgroup M).subtype) (f := M.subtype) M.subtype_injective

/-- A transported `SCN_3(P)` subgroup is nontrivial. -/
public theorem CFSG.section8SylowSubgroupInAmbient_ne_bot_of_mem_scnSubgroups
    [Finite G] {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {M : Subgroup G} (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    section8SylowSubgroupInAmbient M P A ≠ ⊥ := by
  have hA_ne_bot : A ≠ ⊥ :=
    section8_scnSubgroups_ne_bot (p := p) hpodd P.isPGroup' hA
  intro hAambient_bot
  have hAmap_bot : A.map (P : Subgroup M).subtype = ⊥ := by
    rw [← section8SylowSubgroupInAmbient_subgroupOf_eq M P A, hAambient_bot]
    simp
  have hA_bot : A = ⊥ := by
    apply Subgroup.map_injective (P : Subgroup M).subtype_injective
    simpa using hAmap_bot
  exact hA_ne_bot hA_bot

/-- The prime support of a transported `SCN_3(P)` subgroup is the singleton `{p}`. -/
public theorem CFSG.section8_subgroupPrimeSet_sylowSubgroupInAmbient_eq_singleton
    [Finite G] {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {M : Subgroup G} (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    subgroupPrimeSet (section8SylowSubgroupInAmbient M P A) =
      ({⟨p, Fact.out⟩} : Set Nat.Primes) :=
  section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
    (section8SylowSubgroupInAmbient_isPGroup M P A)
    (section8SylowSubgroupInAmbient_ne_bot_of_mem_scnSubgroups hpodd P hA)

/-- A normal subgroup inclusion gives a one-step Section 7 subnormal chain. -/
public theorem CFSG.section8_isSubnormalIn_of_normal_subgroupOf
    {A P : Subgroup G} (hAP : A ≤ P) [hAPnorm : (A.subgroupOf P).Normal] :
    IsSubnormalIn A P := by
  refine ⟨1, ![A, P], by simp, by simp, ?_, ?_⟩
  · intro i
    fin_cases i
    simpa using hAP
  · intro i
    fin_cases i
    change (A.subgroupOf P).Normal
    exact (inferInstance : (A.subgroupOf P).Normal)

/-- In a finite group satisfying the normalizer condition, every subgroup is subnormal
in Mathlib's inductive sense. -/
public theorem CFSG.section8_isSubnormal_of_normalizerCondition
    [Finite G] (hnc : NormalizerCondition G) (H : Subgroup G) :
    H.IsSubnormal := by
  classical
  let m := Nat.card G - Nat.card H
  have hmain :
      ∀ n : ℕ, ∀ H : Subgroup G, Nat.card G - Nat.card H = n → H.IsSubnormal := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H hmeasure
      by_cases htop : H = ⊤
      · simp [htop]
      · let K : Subgroup G := Subgroup.normalizer (H : Set G)
        have hHtop_lt : H < (⊤ : Subgroup G) := lt_top_iff_ne_top.mpr htop
        have hHKlt : H < K := hnc H hHtop_lt
        have hKsub : K.IsSubnormal := by
          by_cases hKtop : K = ⊤
          · simp [hKtop]
          · have hcardHGtop : Nat.card H < Nat.card (⊤ : Subgroup G) :=
              natCard_lt_of_subgroup_lt hHtop_lt
            have hcardHG : Nat.card H < Nat.card G := by
              simpa using hcardHGtop
            have hcardHK : Nat.card H < Nat.card K := natCard_lt_of_subgroup_lt hHKlt
            have hmeasure_lt : Nat.card G - Nat.card K < n := by
              rw [← hmeasure]
              exact Nat.sub_lt_sub_left hcardHG hcardHK
            exact ih (Nat.card G - Nat.card K) hmeasure_lt K rfl
        have hnormal : (H.subgroupOf K).Normal := by
          dsimp [K]
          infer_instance
        exact Subgroup.IsSubnormal.step (G := G) H K hHKlt.le hKsub hnormal
  exact hmain m H rfl

/-- Convert Mathlib's subnormal chain inside an overgroup to the explicit Section 7
ambient-chain formulation. -/
public theorem CFSG.section8_isSubnormalIn_of_subgroupOf_isSubnormal
    [Finite G] {A P : Subgroup G} (hAP : A ≤ P)
    (hsub : (A.subgroupOf P).IsSubnormal) :
    IsSubnormalIn A P := by
  classical
  rcases Subgroup.IsSubnormal.exists_chain hsub with ⟨n, f, hmono, hnorm, h0, hn⟩
  refine ⟨n, fun i => (f i.val).map P.subtype, ?_, ?_, ?_, ?_⟩
  · change (f 0).map P.subtype = A
    rw [h0]
    exact Subgroup.map_subgroupOf_eq_of_le hAP
  · change (f n).map P.subtype = P
    rw [hn]
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨xP, _hxTop, rfl⟩
      exact xP.property
    · intro hxP
      exact Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, by simp, rfl⟩
  · intro i
    exact Subgroup.map_mono (hmono (Nat.le_succ i.val))
  · intro i
    let H0 : Subgroup P := f i.val
    let H1 : Subgroup P := f (i.val + 1)
    have hle : H0 ≤ H1 := hmono (Nat.le_succ i.val)
    have hnorm01 : (H0.subgroupOf H1).Normal := by
      simpa [H0, H1] using hnorm i.val
    have hmap_le : H0.map P.subtype ≤ H1.map P.subtype := Subgroup.map_mono hle
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hmap_le).mpr ?_
    intro x hx
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hy
    rcases Subgroup.mem_map.mp hx with ⟨xP, hxP, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨yP, hyP, rfl⟩
    let xH1 : H1 := ⟨xP, hxP⟩
    let yH1 : H1 := ⟨yP, hle hyP⟩
    have hySub : yH1 ∈ H0.subgroupOf H1 := by
      change yP ∈ H0
      exact hyP
    have hconjSub : xH1 * yH1 * xH1⁻¹ ∈ H0.subgroupOf H1 :=
      Subgroup.Normal.conj_mem hnorm01 yH1 hySub xH1
    have hconjP : (xP * yP * xP⁻¹ : P) ∈ H0 := by
      change ((xH1 * yH1 * xH1⁻¹ : H1) : P) ∈ H0 at hconjSub
      simpa [xH1, yH1, mul_assoc] using hconjSub
    exact Subgroup.mem_map.mpr ⟨(xP * yP * xP⁻¹ : P), hconjP, rfl⟩

/-- Every subgroup of a finite nilpotent overgroup is subnormal in the explicit Section 7
sense. -/
public theorem CFSG.section8_isSubnormalIn_of_nilpotent
    [Finite G] {A P : Subgroup G} (hAP : A ≤ P)
    [Group.IsNilpotent P] :
    IsSubnormalIn A P := by
  have hsub : (A.subgroupOf P).IsSubnormal :=
    section8_isSubnormal_of_normalizerCondition
      (G := P) Group.normalizerCondition_of_isNilpotent (A.subgroupOf P)
  exact section8_isSubnormalIn_of_subgroupOf_isSubnormal hAP hsub

/-- `C_{F(M)}(A₀)` is subnormal in the nilpotent group `F(M)`. -/
public theorem CFSG.section8CentralizerInFitting_isSubnormalIn_fitting
    [Finite G] (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M)) :
    IsSubnormalIn (section8CentralizerInFitting M A₀) (section8FittingSubgroup M) := by
  let : Group.IsNilpotent (section8FittingSubgroup M) :=
    section8FittingSubgroup_isNilpotent M
  exact section8_isSubnormalIn_of_nilpotent (section8CentralizerInFitting_le M A₀)

/-- Members of `section8MaximalSubgroups` are proper. -/
public theorem CFSG.section8MaximalSubgroups_ne_top {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G) :
    M ≠ ⊤ :=
  hM.ne_top

/-- Maximality for members of `section8MaximalSubgroups`. -/
public theorem CFSG.section8MaximalSubgroups_eq_of_le {M H : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G) (hMH : M ≤ H) (hH : H ≠ ⊤) :
    H = M :=
  (hM.le_iff_eq hH).mp hMH

/-- Any subgroup contained in a maximal proper subgroup of `G` is proper. -/
public theorem CFSG.section8_ne_top_of_le_maximal {H M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G) (hHM : H ≤ M) :
    H ≠ ⊤ := by
  intro hHtop
  have htop_le_M : (⊤ : Subgroup G) ≤ M := by
    simpa [hHtop] using hHM
  exact hM.ne_top (top_le_iff.mp htop_le_M)

/-- The transported centralizer inside `F(M)` is proper in `G`. -/
public theorem CFSG.section8CentralizerInFitting_ne_top
    {M : Subgroup G} (hM : M ∈ section8MaximalSubgroups G)
    (A₀ : Subgroup (section8FittingSubgroup M)) :
    section8CentralizerInFitting M A₀ ≠ ⊤ :=
  section8_ne_top_of_le_maximal hM (section8CentralizerInFitting_le_maximal M A₀)

/-- The easy part of verifying Hypothesis 7.1 for `C_{F(M)}(A₀)`: after the
generated-core equality is proved for every proper overgroup, the nontriviality and
properness conditions follow from the Section 8 hypotheses. -/
public theorem CFSG.section8CentralizerInFitting_Hypothesis7_1_of_generated_eq
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hgen :
      ∀ X : Subgroup G,
        section8CentralizerInFitting M A₀ ≤ X → X ≠ ⊤ →
          section7Generated X (section8CentralizerInFitting M A₀)
              (subgroupPrimeSet (section8CentralizerInFitting M A₀))ᶜ =
            piCoreIn (subgroupPrimeSet (section8CentralizerInFitting M A₀))ᶜ X) :
    Hypothesis7_1 (section8CentralizerInFitting M A₀) :=
  ⟨section8CentralizerInFitting_ne_bot_of_rank hA₀ hA₀rank,
    section8CentralizerInFitting_ne_top hM A₀, hgen⟩


/-- Build membership in `U` from an explicit unique maximal overgroup. -/
public theorem CFSG.section8UniqueSubgroups_of_forall_maximal
    {H M : Subgroup G} (hHproper : H ≠ ⊤) (hM : M ∈ section8MaximalSubgroups G)
    (hHM : H ≤ M)
    (huniq : ∀ N : Subgroup G, N ∈ section8MaximalSubgroupsContaining H → N = M) :
    H ∈ section8UniqueSubgroups G := by
  refine ⟨hHproper, M, ?_⟩
  ext N
  constructor
  · intro hN
    simp [huniq N hN]
  · intro hN
    have hNM : N = M := by
      simpa using hN
    subst N
    exact ⟨hM, hHM⟩

/-- A normalizer criterion for membership in `U`. -/
public theorem CFSG.section8UniqueSubgroups_of_forall_le_normalizer_eq
    {H L M : Subgroup G} (hHproper : H ≠ ⊤) (hM : M ∈ section8MaximalSubgroups G)
    (hHM : H ≤ M) (hnorm : Subgroup.normalizer (L : Set G) = M)
    (hNnorm :
      ∀ N : Subgroup G, N ∈ section8MaximalSubgroupsContaining H →
        N ≤ Subgroup.normalizer (L : Set G)) :
    H ∈ section8UniqueSubgroups G := by
  refine section8UniqueSubgroups_of_forall_maximal hHproper hM hHM ?_
  intro N hN
  have hNM : N ≤ M := by
    simpa [hnorm] using hNnorm N hN
  exact ((hN.1.le_iff_eq hM.1).mp hNM).symm


public theorem CFSG.section8_primeRank_le_of_subgroup
    [Finite G] (S : Subgroup G) (q : ℕ) :
    primeRank q S ≤ primeRank q G := by
  classical
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := S), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, hAp, hAcomm, hnA⟩
    let A' : Subgroup G := A.map S.subtype
    have hA'p : IsPGroup q A' := IsPGroup.map hAp S.subtype
    have hA'comm : IsMulCommutative A' := by
      let : IsMulCommutative A := hAcomm
      simpa [A'] using (Subgroup.map_isMulCommutative (f := S.subtype) (H := A))
    have hgen_eq : generatorRank A' = generatorRank A := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      let e : A ≃* A' :=
        Subgroup.equivMapOfInjective (f := S.subtype) A S.subtype_injective
      exact (Group.rank_congr e).symm
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card G, ?_⟩
      intro m hm
      rcases hm with ⟨B, _hBp, _hBcomm, hmB⟩
      exact hmB.trans <|
        (section8_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hnA⟩

public theorem CFSG.section8_groupRank_le_of_subgroup
    [Finite G] (S : Subgroup G) :
    groupRank S ≤ groupRank G := by
  classical
  have hprimeRank_le_natCard : ∀ q : ℕ, primeRank q G ≤ Nat.card G := by
    intro q
    rw [primeRank]
    refine csSup_le ?_ ?_
    · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := G), inferInstance, Nat.zero_le _⟩
    · intro n hn
      rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
      exact hnA.trans <|
        (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  rw [groupRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, 2, by decide, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨q, hq, hnq⟩
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card G, ?_⟩
      intro m hm
      rcases hm with ⟨r, _hr, hmr⟩
      exact hmr.trans (hprimeRank_le_natCard r)
    · exact ⟨q, hq, hnq.trans (section8_primeRank_le_of_subgroup S q)⟩

/-- In a minimal counterexample, the centralizer of a nonidentity singleton is proper. -/
public theorem CFSG.section8_centralizer_singleton_ne_top_of_ne_one
    [Finite G] [IsMinCE G] {z : G} (hz : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have hz_center : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hycent : y ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top y
    exact ((Subgroup.mem_centralizer_iff.mp hycent) z (by simp)).symm
  have hz_eq_one : z = 1 := by
    have hzbot : z ∈ (⊥ : Subgroup G) := by
      simpa [center_eq_bot_of_min_ce (G := G)] using hz_center
    simpa using hzbot
  exact hz hz_eq_one

/-- A nonidentity subgroup normal in a maximal subgroup has normalizer that maximal subgroup. -/
public theorem CFSG.section8_normalizer_eq_of_nontrivial_normal_in_maximal
    [Finite G] [IsMinCE G] {M L : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G) (hLM : L ≤ M) (hL_ne_bot : L ≠ ⊥)
    (hLnormM : (L.subgroupOf M).Normal) :
    Subgroup.normalizer (L : Set G) = M := by
  have hM_le_norm : M ≤ Subgroup.normalizer (L : Set G) := by
    let : (L.subgroupOf M).Normal := hLnormM
    exact Subgroup.le_normalizer_of_normal_subgroupOf hLM
  have hnorm_ne_top : Subgroup.normalizer (L : Set G) ≠ ⊤ := by
    intro hnorm_top
    have hLnorm : L.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
    let : IsSimpleGroup G := IsMinCE.simple
    rcases (haveI := hLnorm; IsSimpleGroup.eq_bot_or_eq_top_of_normal L) with hLbot | hLtop
    · exact hL_ne_bot hLbot
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [hLtop] using hLM
      exact hM.1 (top_le_iff.mp htop_le_M)
  exact section8MaximalSubgroups_eq_of_le hM hM_le_norm hnorm_ne_top

/-- A transported nontrivial normal subgroup of a maximal subgroup has ambient normalizer `M`. -/
public theorem CFSG.section8_normalizer_subgroupInAmbient_eq_of_nontrivial_normal_in_maximal
    [Finite G] [IsMinCE G] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G) {K : Subgroup M}
    (hK_ne_bot : K ≠ ⊥) (hKnorm : K.Normal) :
    Subgroup.normalizer (section8SubgroupInAmbient K : Set G) = M :=
  section8_normalizer_eq_of_nontrivial_normal_in_maximal hM
    (section8SubgroupInAmbient_le K)
    (by
      intro hKambient
      exact hK_ne_bot ((section8SubgroupInAmbient_eq_bot_iff K).1 hKambient))
    (section8SubgroupInAmbient_normal_in hKnorm)

/-- In branch (b), the ambient normalizer of `Z(J(P))` is the maximal subgroup `M`. -/
public theorem CFSG.section8_normalizer_centerIn_thompsonSubgroup_eq_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) :
    Subgroup.normalizer
        (section8SubgroupInAmbient (centerIn (thompsonSubgroup P) : Subgroup M) : Set G) = M := by
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ :=
    section8_sylow_ne_bot_of_mem_fitting_primeSet_of_fitting_isPGroup hpF hFp P
  have hZJ_ne_bot : (centerIn (thompsonSubgroup P) : Subgroup M) ≠ ⊥ :=
    section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot P.isPGroup' hP_ne_bot
  have hZJ_norm : (centerIn (thompsonSubgroup P) : Subgroup M).Normal :=
    section8_centerIn_thompsonSubgroup_normal_of_fitting_isPGroup hM hFp P
  exact
    section8_normalizer_subgroupInAmbient_eq_of_nontrivial_normal_in_maximal
      hM hZJ_ne_bot hZJ_norm

/-- A characteristic subgroup is normalized by every ambient element normalizing its parent. -/
public theorem CFSG.section8_normalizer_map_subtype_le_of_characteristic
    [Finite G] {H : Subgroup G} {K : Subgroup H} [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  intro g hgH
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hxK
  rcases Subgroup.mem_map.mp hxK with ⟨y, hyK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, hgH⟩
  let φH : H ≃* H := H.normalizerMonoidHom gH
  have hφK : K.map φH.toMonoidHom ≤ K :=
    (Subgroup.characteristic_iff_map_le.mp (inferInstance : K.Characteristic)) φH
  have hyK' : φH y ∈ K := hφK (Subgroup.mem_map_of_mem φH.toMonoidHom hyK)
  have hmem : ((φH y : H) : G) ∈ K.map H.subtype :=
    Subgroup.mem_map_of_mem H.subtype hyK'
  simpa [φH, gH, Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem

/-- The ambient copy of `Z(F(M))` is normal inside the maximal subgroup `M`. -/
public theorem CFSG.section8CenterInFitting_normal_in_maximal
    [Finite G] (M : Subgroup G) :
    ((section8CenterInFitting M).subgroupOf M).Normal := by
  have hFNorm : ((section8FittingSubgroup M).subgroupOf M).Normal :=
    section8FittingSubgroup_normal_in M
  have hM_le_normF : M ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
    let : ((section8FittingSubgroup M).subgroupOf M).Normal := hFNorm
    exact Subgroup.le_normalizer_of_normal_subgroupOf (section8FittingSubgroup_le M)
  have hnormF_le_normZ :
      Subgroup.normalizer (section8FittingSubgroup M : Set G) ≤
        Subgroup.normalizer (section8CenterInFitting M : Set G) := by
    simpa [section8CenterInFitting, centerIn_eq_map_center_local] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := section8FittingSubgroup M)
        (K := Subgroup.center (section8FittingSubgroup M)))
  exact
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (section8CenterInFitting_le_maximal M)).mpr
      (hM_le_normF.trans hnormF_le_normZ)

/-- In branch (b), the ambient normalizer of `Z(F(M))` is `M`. -/
public theorem CFSG.section8_normalizer_centerInFitting_eq_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M)) :
    Subgroup.normalizer (section8CenterInFitting M : Set G) = M := by
  have hZ_ne_bot : section8CenterInFitting M ≠ ⊥ :=
    section8_centerIn_ne_bot_of_isPGroup hFp
      (section8_ne_bot_of_mem_subgroupPrimeSet hpF)
  exact
    section8_normalizer_eq_of_nontrivial_normal_in_maximal hM
      (section8CenterInFitting_le_maximal M) hZ_ne_bot
      (section8CenterInFitting_normal_in_maximal M)

/-- In branch (b), `Z(F(M))` lies in every transported member of `SCN_3(P)`. -/
public theorem CFSG.section8CenterInFitting_le_sylowSubgroupInAmbient_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    section8CenterInFitting M ≤ section8SylowSubgroupInAmbient M P A := by
  intro z hzZ
  rcases hzZ with ⟨hzF, hzCentF⟩
  have hzPambient : z ∈ section8SubgroupInAmbient (P : Subgroup M) :=
    section8FittingSubgroup_le_sylow hFp P hzF
  rcases Subgroup.mem_map.mp hzPambient with ⟨y, hyP, hyz⟩
  let yP : (P : Subgroup M) := ⟨y, hyP⟩
  have hyP_cent : yP ∈ Subgroup.centralizer (A : Set (P : Subgroup M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haAmbient : (((a : (P : Subgroup M)) : M) : G) ∈
        section8SylowSubgroupInAmbient M P A := by
      change (((a : (P : Subgroup M)) : M) : G) ∈
        ((A.map (P : Subgroup M).subtype).map M.subtype)
      exact Subgroup.mem_map.mpr
        ⟨((a : (P : Subgroup M)) : M),
          Subgroup.mem_map_of_mem (P : Subgroup M).subtype ha, rfl⟩
    have haF : (((a : (P : Subgroup M)) : M) : G) ∈ section8FittingSubgroup M :=
      section8SylowSubgroupInAmbient_le_fitting_of_isPGroup hM hFp P hA haAmbient
    have hcommG : (((a : (P : Subgroup M)) : M) : G) * ((y : M) : G) =
        ((y : M) : G) * (((a : (P : Subgroup M)) : M) : G) := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hzCentF
        (((a : (P : Subgroup M)) : M) : G) haF
      simpa [← hyz] using hcomm
    apply Subtype.ext
    apply Subtype.ext
    exact hcommG
  have hyA : yP ∈ A := by
    simpa [hA.2.1] using hyP_cent
  change z ∈ ((A.map (P : Subgroup M).subtype).map M.subtype)
  exact Subgroup.mem_map.mpr
    ⟨y, Subgroup.mem_map_of_mem (P : Subgroup M).subtype hyA, hyz⟩

/-- In branch (b), the centralizer of a transported `SCN_3(P)` subgroup is contained in `M`. -/
public theorem CFSG.section8_centralizer_sylowSubgroupInAmbient_le_maximal_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    Subgroup.centralizer (section8SylowSubgroupInAmbient M P A : Set G) ≤ M := by
  have hZ_le_A : section8CenterInFitting M ≤ section8SylowSubgroupInAmbient M P A :=
    section8CenterInFitting_le_sylowSubgroupInAmbient_of_fitting_isPGroup hM hFp P hA
  have hZnorm : Subgroup.normalizer (section8CenterInFitting M : Set G) = M :=
    section8_normalizer_centerInFitting_eq_of_fitting_isPGroup hM hpF hFp
  intro g hg
  have hgNormZ : g ∈ Subgroup.normalizer (section8CenterInFitting M : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro z hzZ
    have hzA : z ∈ section8SylowSubgroupInAmbient M P A := hZ_le_A hzZ
    have hcomm := Subgroup.mem_centralizer_iff.mp hg z hzA
    have hconj : g * z * g⁻¹ = z := by
      calc
        g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hcomm]
        _ = z := by simp [mul_assoc]
    simpa [hconj] using hzZ
  rw [hZnorm] at hgNormZ
  exact hgNormZ

/-- In branch (b), the internal centralizer in `M` maps onto the ambient centralizer. -/
public theorem CFSG.section8_centralizer_sylowSubgroupInAmbient_subgroupOf_map_eq
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    (Subgroup.centralizer (A.map (P : Subgroup M).subtype : Set M)).map M.subtype =
      Subgroup.centralizer (section8SylowSubgroupInAmbient M P A : Set G) := by
  let A_M : Subgroup M := A.map (P : Subgroup M).subtype
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  have hC_le_M : Subgroup.centralizer (A_G : Set G) ≤ M :=
    section8_centralizer_sylowSubgroupInAmbient_le_maximal_of_fitting_isPGroup
      hM hpF hFp P hA
  change (Subgroup.centralizer (A_M : Set M)).map M.subtype =
      Subgroup.centralizer (A_G : Set G)
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyC, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Subgroup.mem_centralizer_iff] at hyC
    rcases Subgroup.mem_map.mp ha with ⟨aM, haA_M, rfl⟩
    exact congrArg Subtype.val (hyC aM haA_M)
  · intro hx
    have hxM : x ∈ M := hC_le_M hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro aM haA_M
    apply Subtype.ext
    rw [Subgroup.mem_centralizer_iff] at hx
    have haA_G : (aM : G) ∈ A_G := by
      change (aM : G) ∈ (A_M.map M.subtype)
      exact Subgroup.mem_map_of_mem M.subtype haA_M
    exact hx (aM : G) haA_G

/-- In branch (b), the transported `p'`-core of the centralizer of `A` is trivial. -/
public theorem CFSG.section8_pPrimeCore_centralizer_sylowSubgroupInAmbient_eq_bot_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    (pPrimeCore p
        (Subgroup.centralizer (section8SylowSubgroupInAmbient M P A : Set G))).map
      (Subgroup.centralizer (section8SylowSubgroupInAmbient M P A : Set G)).subtype = ⊥ := by
  let A_M : Subgroup M := A.map (P : Subgroup M).subtype
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  let C_M : Subgroup M := Subgroup.centralizer (A_M : Set M)
  let C_G : Subgroup G := Subgroup.centralizer (A_G : Set G)
  have hCmap : C_M.map M.subtype = C_G := by
    simpa [C_M, C_G, A_M, A_G] using
      section8_centralizer_sylowSubgroupInAmbient_subgroupOf_map_eq hM hpF hFp P hA
  have hcoreM : pPrimeCore p M = ⊥ :=
    section8_pPrimeCore_eq_bot_of_fitting_isPGroup hM hFp
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hA_M_p : IsPGroup p A_M := by
    simpa [A_M] using IsPGroup.map (P.isPGroup'.to_subgroup A) (P : Subgroup M).subtype
  have hcoreC_M_map_le : (pPrimeCore p C_M).map C_M.subtype ≤ pPrimeCore p M := by
    simpa [C_M] using (proposition_1_15_b (G := M) hsolvM p A_M hA_M_p)
  have hcoreC_M_map_bot : (pPrimeCore p C_M).map C_M.subtype = ⊥ := by
    apply le_bot_iff.mp
    simpa [hcoreM] using hcoreC_M_map_le
  have hcoreC_M_bot : pPrimeCore p C_M = ⊥ := by
    apply Subgroup.map_injective C_M.subtype_injective
    simpa using hcoreC_M_map_bot
  let e0 : C_M ≃* C_M.map M.subtype :=
    Subgroup.equivMapOfInjective (f := M.subtype) C_M M.subtype_injective
  let e : C_M ≃* C_G := e0.trans (MulEquiv.subgroupCongr hCmap)
  have hcoreC_G_bot : pPrimeCore p C_G = ⊥ := by
    have hmap := pPrimeCore_map_iso (G := C_M) (G' := C_G) (p := p) e
    simpa [hcoreC_M_bot] using hmap.symm
  change (pPrimeCore p C_G).map C_G.subtype = ⊥
  simp [hcoreC_G_bot]

/-- For a singleton complement, `piCoreIn` is the transported `p'`-core. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_eq_pPrimeCore_map
    [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G) :
    piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H =
      (pPrimeCore p H).map H.subtype := by
  let Sπ : Set (Subgroup H) :=
    {K | K.Normal ∧ IsPiSubgroup (G := H) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) K}
  let Sp : Set (Subgroup H) := {K | K.Normal ∧ Nat.Coprime p (Nat.card K)}
  have hsets : Sπ = Sp := by
    ext K
    constructor
    · rintro ⟨hKnorm, hKπ⟩
      have hcop : Nat.Coprime p (Nat.card K) := by
        refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 ?_
        intro hpK
        have hpmem : (⟨p, Fact.out⟩ : Nat.Primes) ∈
            (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) :=
          hKπ ⟨p, Fact.out⟩ hpK
        exact hpmem (Set.mem_singleton _)
      exact ⟨hKnorm, hcop⟩
    · rintro ⟨hKnorm, hKcop⟩
      have hKπ :
          IsPiSubgroup (G := H) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) K := by
        intro q hq
        simp only [Set.mem_compl_iff]
        intro hqeq
        subst q
        exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hKcop) hq
      exact ⟨hKnorm, hKπ⟩
  calc
    piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H
        = (piCore (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H).map H.subtype := rfl
    _ = (sSup Sπ).map H.subtype := rfl
    _ = (sSup Sp).map H.subtype := by rw [hsets]
    _ = (pPrimeCore p H).map H.subtype := rfl

/-- In branch (b), the Section 7 `p'`-core of the centralizer of `A` is trivial. -/
public theorem CFSG.section8_piCoreIn_centralizer_sylowSubgroupInAmbient_singleton_compl_eq_bot
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ)
      (Subgroup.centralizer (section8SylowSubgroupInAmbient M P A : Set G)) = ⊥ := by
  simpa [section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using
    section8_pPrimeCore_centralizer_sylowSubgroupInAmbient_eq_bot_of_fitting_isPGroup
      hM hpF hFp P hA

/-- Membership in `SCN_3` transports across a multiplicative equivalence of finite
`p`-groups. -/
public theorem CFSG.section8_scnSubgroups_three_map_equiv_of_isPGroup
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (hRp : IsPGroup p R) (e : R ≃* S) {A : Subgroup R}
    (hA : A ∈ scnSubgroups 3 R) :
    A.map e.toMonoidHom ∈ scnSubgroups 3 S := by
  rcases hA with ⟨hAnorm, hAcent, hArank⟩
  have hA' : A ∈ scnSubgroups 3 R := ⟨hAnorm, hAcent, hArank⟩
  let Amap : Subgroup S := A.map e.toMonoidHom
  refine ⟨?_, ?_, ?_⟩
  · exact Subgroup.Normal.map hAnorm e.toMonoidHom e.surjective
  · ext s
    constructor
    · intro hs
      have hesym_cent : e.symm s ∈ Subgroup.centralizer (A : Set R) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hsa :=
          Subgroup.mem_centralizer_iff.mp hs (e a)
            (Subgroup.mem_map_of_mem e.toMonoidHom ha)
        apply e.injective
        simpa using hsa
      have hesym_A : e.symm s ∈ A := by
        simpa [hAcent] using hesym_cent
      exact Subgroup.mem_map.mpr ⟨e.symm s, hesym_A, by simp⟩
    · intro hs
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rcases Subgroup.mem_map.mp hs with ⟨a, haA, rfl⟩
      rcases Subgroup.mem_map.mp ht with ⟨b, hbA, rfl⟩
      have ha_cent : a ∈ Subgroup.centralizer (A : Set R) := by
        simpa [hAcent] using haA
      simpa using congrArg e (Subgroup.mem_centralizer_iff.mp ha_cent b hbA)
  · have hAcomm : IsMulCommutative A :=
      (scnSubgroup_normal_commutative (p := p) hRp hA').2
    have hAmap_comm : IsMulCommutative Amap := by
      let : IsMulCommutative A := hAcomm
      simpa [Amap] using (Subgroup.map_isMulCommutative (f := e.toMonoidHom) (H := A))
    have hAmap_p : IsPGroup p Amap := by
      simpa [Amap] using IsPGroup.map (hRp.to_subgroup A) e.toMonoidHom
    have hgen_eq : generatorRank Amap = generatorRank A := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      let eA : A ≃* Amap :=
        Subgroup.equivMapOfInjective (f := e.toMonoidHom) A e.injective
      exact (Group.rank_congr eA).symm
    have hAgen : 3 ≤ generatorRank A :=
      scnSubgroup_generatorRank_at_least_three (p := p) hpodd hRp hA'
    exact
      groupRank_at_least_three_of_generatorRank_subgroup
        (q := p) Fact.out (le_rfl : Amap ≤ Amap) hAmap_p hAmap_comm
        (by simpa [hgen_eq] using hAgen)

/-- The transported `A ∈ SCN_3(P)` remains an `SCN_3` subgroup of the transported Sylow
subgroup. -/
public theorem CFSG.section8SylowSubgroupInAmbient_subgroupOf_sylowImage_mem_scnSubgroups
    [Finite G] {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {M : Subgroup G} (P : Sylow p M)
    {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    (section8SylowSubgroupInAmbient M P A).subgroupOf
      (section8SubgroupInAmbient (P : Subgroup M)) ∈
        scnSubgroups 3 (section8SubgroupInAmbient (P : Subgroup M)) := by
  let P_G : Subgroup G := section8SubgroupInAmbient (P : Subgroup M)
  let e : (P : Subgroup M) ≃* P_G :=
    Subgroup.equivMapOfInjective (f := M.subtype) (P : Subgroup M) M.subtype_injective
  have hAmap_eq : A.map e.toMonoidHom =
      (section8SylowSubgroupInAmbient M P A).subgroupOf P_G := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
      change ((a : M) : G) ∈ section8SylowSubgroupInAmbient M P A
      change ((a : M) : G) ∈ ((A.map (P : Subgroup M).subtype).map M.subtype)
      exact Subgroup.mem_map.mpr
        ⟨(a : M), Subgroup.mem_map_of_mem (P : Subgroup M).subtype haA, rfl⟩
    · intro hx
      change (x : G) ∈ section8SylowSubgroupInAmbient M P A at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyAmap, hyx⟩
      rcases Subgroup.mem_map.mp hyAmap with ⟨a, haA, hay⟩
      refine Subgroup.mem_map.mpr ⟨a, haA, ?_⟩
      apply Subtype.ext
      exact hyx ▸ congrArg Subtype.val hay
  have hmap_scn : A.map e.toMonoidHom ∈ scnSubgroups 3 P_G :=
    section8_scnSubgroups_three_map_equiv_of_isPGroup hpodd P.isPGroup' e hA
  simpa [P_G, ← hAmap_eq] using hmap_scn

/-- The characteristic copy of `Z(J(P))` inside the transported Sylow subgroup maps to the
ambient transported subgroup used in Section 8. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_image_eq
    {M : Subgroup G} {p : ℕ} (P : Sylow p M) :
    let P₀sub : Subgroup G := section8SubgroupInAmbient (P : Subgroup M)
    let K : Subgroup M := centerIn (thompsonSubgroup P)
    let Kp : Subgroup (P : Subgroup M) := K.subgroupOf (P : Subgroup M)
    let e : (P : Subgroup M) ≃* P₀sub :=
      Subgroup.equivMapOfInjective (f := M.subtype) (P : Subgroup M) M.subtype_injective
    (Kp.map e.toMonoidHom).map P₀sub.subtype = section8SubgroupInAmbient K := by
  intro P₀sub K Kp e
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hzKp, hz_eq⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨((z : (P : Subgroup M)) : M), hzKp, ?_⟩
    exact congrArg Subtype.val hz_eq
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
    have hyP : y ∈ (P : Subgroup M) :=
      (inf_le_left.trans (section8_thompsonSubgroup_le (P : Subgroup M))) hyK
    let z : (P : Subgroup M) := ⟨y, hyP⟩
    have hzKp : z ∈ Kp := hyK
    refine Subgroup.mem_map.mpr ?_
    refine ⟨e z, Subgroup.mem_map_of_mem e.toMonoidHom hzKp, ?_⟩
    rfl

/-- The ambient copy of `Z(J(P))` can be computed canonically from the transported
Sylow subgroup itself. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_ambient_eq_top_image
    {M : Subgroup G} {p : ℕ} (P : Sylow p M) :
    section8SubgroupInAmbient (centerIn (thompsonSubgroup P) : Subgroup M) =
      (centerIn (thompsonSubgroup
          (⊤ : Subgroup (section8SubgroupInAmbient (P : Subgroup M))))).map
        (section8SubgroupInAmbient (P : Subgroup M)).subtype := by
  let P₀sub : Subgroup G := section8SubgroupInAmbient (P : Subgroup M)
  let K : Subgroup M := centerIn (thompsonSubgroup P)
  let Kp : Subgroup (P : Subgroup M) := K.subgroupOf (P : Subgroup M)
  let e : (P : Subgroup M) ≃* P₀sub :=
    Subgroup.equivMapOfInjective (f := M.subtype) (P : Subgroup M) M.subtype_injective
  have hKp : Kp = centerIn (thompsonSubgroup (⊤ : Subgroup (P : Subgroup M))) := by
    simpa [Kp, K] using
      section8_centerIn_thompsonSubgroup_subgroupOf_eq_top (S := (P : Subgroup M))
  have hmap :
      Kp.map e.toMonoidHom = centerIn (thompsonSubgroup (⊤ : Subgroup P₀sub)) := by
    rw [hKp]
    exact section8_centerIn_thompsonSubgroup_top_map_equiv e
  have himage :
      (Kp.map e.toMonoidHom).map P₀sub.subtype = section8SubgroupInAmbient K := by
    simpa [P₀sub, K, Kp, e] using section8_centerIn_thompsonSubgroup_image_eq P
  calc
    section8SubgroupInAmbient (centerIn (thompsonSubgroup P) : Subgroup M)
        = section8SubgroupInAmbient K := by rfl
    _ = (Kp.map e.toMonoidHom).map P₀sub.subtype := himage.symm
    _ = (centerIn (thompsonSubgroup (⊤ : Subgroup P₀sub))).map P₀sub.subtype := by rw [hmap]
    _ = (centerIn (thompsonSubgroup
          (⊤ : Subgroup (section8SubgroupInAmbient (P : Subgroup M))))).map
        (section8SubgroupInAmbient (P : Subgroup M)).subtype := by rfl

/-- If two Sylow subgroups have the same transported ambient subgroup, then the transported
copies of `Z(J(-))` agree. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_eq_of_sylow_ambient_eq
    {M N : Subgroup G} {p : ℕ} (P : Sylow p M) (R : Sylow p N)
    (hPR :
      section8SubgroupInAmbient (P : Subgroup M) =
        section8SubgroupInAmbient (R : Subgroup N)) :
    section8SubgroupInAmbient (centerIn (thompsonSubgroup P) : Subgroup M) =
      section8SubgroupInAmbient (centerIn (thompsonSubgroup R) : Subgroup N) := by
  rw [section8_centerIn_thompsonSubgroup_ambient_eq_top_image P,
    section8_centerIn_thompsonSubgroup_ambient_eq_top_image R, hPR]

/-- The characteristic transfer \(N_G(P)\le N_G(Z(J(P)))\) used in part (b). -/
public theorem CFSG.section8_normalizer_centerIn_thompsonSubgroup_le_of_normalizer_sylow
    [Finite G] {M : Subgroup G} {p : ℕ} (P : Sylow p M) :
    Subgroup.normalizer (section8SubgroupInAmbient (P : Subgroup M) : Set G) ≤
      Subgroup.normalizer
        (section8SubgroupInAmbient (centerIn (thompsonSubgroup P) : Subgroup M) :
          Set G) := by
  let P₀sub : Subgroup G := section8SubgroupInAmbient (P : Subgroup M)
  let K : Subgroup M := centerIn (thompsonSubgroup P)
  let Kp : Subgroup (P : Subgroup M) := K.subgroupOf (P : Subgroup M)
  let e : (P : Subgroup M) ≃* P₀sub :=
    Subgroup.equivMapOfInjective (f := M.subtype) (P : Subgroup M) M.subtype_injective
  let Kimage : Subgroup P₀sub := Kp.map e.toMonoidHom
  have : Kp.Characteristic :=
    section8_centerIn_thompsonSubgroup_subgroupOf_characteristic (P : Subgroup M)
  have : Kimage.Characteristic := section8_characteristic_map_equiv Kp e
  have hnorm :
      Subgroup.normalizer (P₀sub : Set G) ≤
        Subgroup.normalizer (Kimage.map P₀sub.subtype : Set G) :=
    section8_normalizer_map_subtype_le_of_characteristic (H := P₀sub) (K := Kimage)
  have himage : Kimage.map P₀sub.subtype = section8SubgroupInAmbient K :=
    section8_centerIn_thompsonSubgroup_image_eq P
  rw [himage] at hnorm
  simpa [P₀sub, K] using hnorm

/-- A normalizer-control criterion showing that the transported Sylow subgroup of `M`
is Sylow in `G`. -/
public theorem CFSG.section8SubgroupInAmbient_sylow_of_normalizer_le
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G} (P : Sylow p M)
    (hN :
      Subgroup.normalizer (section8SubgroupInAmbient (P : Subgroup M) : Set G) ≤ M) :
    ∃ P₀ : Sylow p G,
      (P₀ : Subgroup G) = section8SubgroupInAmbient (P : Subgroup M) := by
  classical
  let P₀sub : Subgroup G := section8SubgroupInAmbient (P : Subgroup M)
  have hP₀p : IsPGroup p P₀sub := section8SubgroupInAmbient_sylow_isPGroup P
  refine ⟨⟨P₀sub, hP₀p, ?_⟩, rfl⟩
  intro Q hQp hP₀Q
  have hQ_le_P₀ : Q ≤ P₀sub := by
    let K : Subgroup Q := P₀sub.subgroupOf Q
    have : Fact (IsPGroup p Q) := ⟨hQp⟩
    have hQnil : Group.IsNilpotent Q := IsPGroup.isNilpotent (p := p) (G := Q) hQp
    have hnc : NormalizerCondition Q := by
      let : Group.IsNilpotent Q := hQnil
      exact Group.normalizerCondition_of_isNilpotent (G := Q)
    have hnormK_le : Subgroup.normalizer (K : Set Q) ≤ K := by
      intro x hxnorm
      have hxnormP₀ : (x : G) ∈ Subgroup.normalizer (P₀sub : Set G) := by
        refine Subgroup.mem_normalizer_fintype ?_
        intro y hyP₀
        have hyQ : y ∈ Q := hP₀Q hyP₀
        have hyK : (⟨y, hyQ⟩ : Q) ∈ K := hyP₀
        have hconjK :
            x * (⟨y, hyQ⟩ : Q) * x⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hxnorm (⟨y, hyQ⟩ : Q)).1 hyK
        exact hconjK
      have hxM : (x : G) ∈ M := hN hxnormP₀
      let R : Subgroup M := (Q ⊓ M).subgroupOf M
      have hR_p : IsPGroup p R := by
        have hInf_p : IsPGroup p (Q ⊓ M : Subgroup G) := hQp.to_inf_left
        have e : R ≃* (Q ⊓ M : Subgroup G) :=
          Subgroup.subgroupOfEquivOfLe (H := Q ⊓ M) (K := M) inf_le_right
        exact hInf_p.of_equiv e.symm
      have hP_le_R : (P : Subgroup M) ≤ R := by
        intro y hyP
        have hyP₀ : (y : G) ∈ P₀sub :=
          Subgroup.mem_map_of_mem M.subtype hyP
        exact ⟨hP₀Q hyP₀, y.property⟩
      have hR_eq : R = (P : Subgroup M) := P.is_maximal' hR_p hP_le_R
      have hxR : (⟨(x : G), hxM⟩ : M) ∈ R := ⟨x.property, hxM⟩
      have hxP : (⟨(x : G), hxM⟩ : M) ∈ (P : Subgroup M) := by
        simpa [hR_eq] using hxR
      have hxP₀ : (x : G) ∈ P₀sub := Subgroup.mem_map_of_mem M.subtype hxP
      exact hxP₀
    have hnormK_eq : Subgroup.normalizer (K : Set Q) = K :=
      le_antisymm hnormK_le Subgroup.le_normalizer
    have hKtop : K = ⊤ :=
      normalizerCondition_iff_only_full_group_self_normalizing.mp hnc K hnormK_eq
    intro x hxQ
    have hxK : (⟨x, hxQ⟩ : Q) ∈ K := by
      simp [hKtop]
    exact hxK
  exact le_antisymm hQ_le_P₀ hP₀Q

/-- If a global Sylow subgroup lies in a subgroup `N`, then its pullback to `N` is Sylow
in `N`. -/
public theorem CFSG.section8_sylow_subgroupOf_of_global_sylow_le
    {p : ℕ} [Fact p.Prime] {N : Subgroup G} (P₀ : Sylow p G)
    (hP₀N : (P₀ : Subgroup G) ≤ N) :
    ∃ R : Sylow p N, (R : Subgroup N).map N.subtype = (P₀ : Subgroup G) := by
  let Rsub : Subgroup N := (P₀ : Subgroup G).subgroupOf N
  have hRsub_p : IsPGroup p Rsub :=
    P₀.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hP₀N).symm
  have hRsub_max :
      ∀ {Q : Subgroup N}, IsPGroup p Q → Rsub ≤ Q → Q = Rsub := by
    intro Q hQp hRsubQ
    have hQmap_p : IsPGroup p (Q.map N.subtype) := IsPGroup.map hQp N.subtype
    have hP₀_le_Qmap : (P₀ : Subgroup G) ≤ Q.map N.subtype := by
      intro x hxP
      have hxN : x ∈ N := hP₀N hxP
      let xN : N := ⟨x, hxN⟩
      have hxR : xN ∈ Rsub := by
        change x ∈ (P₀ : Subgroup G)
        exact hxP
      exact Subgroup.mem_map_of_mem N.subtype (hRsubQ hxR)
    have hQmap_eq : Q.map N.subtype = (P₀ : Subgroup G) :=
      P₀.is_maximal' hQmap_p hP₀_le_Qmap
    apply Subgroup.map_injective N.subtype_injective
    calc
      Q.map N.subtype = (P₀ : Subgroup G) := hQmap_eq
      _ = Rsub.map N.subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hP₀N]
  refine ⟨⟨Rsub, hRsub_p, ?_⟩, ?_⟩
  · intro Q hQp hRsubQ
    exact hRsub_max hQp hRsubQ
  · exact Subgroup.map_subgroupOf_eq_of_le hP₀N


/-- The branch (b) Sylow endpoint, isolated from the characteristic normalizer-transfer step. -/
public theorem CFSG.section8_part_b_sylow_endpoint
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M)
    (hNtransfer :
      Subgroup.normalizer (section8SubgroupInAmbient (P : Subgroup M) : Set G) ≤
        Subgroup.normalizer
          (section8SubgroupInAmbient (centerIn (thompsonSubgroup P) : Subgroup M) :
            Set G)) :
    ∃ P₀ : Sylow p G,
      (P₀ : Subgroup G) = section8SubgroupInAmbient (P : Subgroup M) := by
  have hZJnorm :
      Subgroup.normalizer
          (section8SubgroupInAmbient (centerIn (thompsonSubgroup P) : Subgroup M) :
            Set G) = M :=
    section8_normalizer_centerIn_thompsonSubgroup_eq_of_fitting_isPGroup
      hM hpF hFp P
  refine section8SubgroupInAmbient_sylow_of_normalizer_le P ?_
  simpa [hZJnorm] using hNtransfer

/-- The first conclusion of branch (b): the transported Sylow subgroup of `M` is Sylow in `G`. -/
public theorem CFSG.section8_part_b_sylow_core
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) :
    ∃ P₀ : Sylow p G,
    (P₀ : Subgroup G) = section8SubgroupInAmbient (P : Subgroup M) :=
  section8_part_b_sylow_endpoint hM hpF hFp P
    (section8_normalizer_centerIn_thompsonSubgroup_le_of_normalizer_sylow P)

/-- In branch (b), each transported `SCN_3(P)` subgroup is a global member of
`SCN_3(p)`. -/
public theorem CFSG.section8SylowSubgroupInAmbient_mem_scnPrimeSubgroups_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    section8SylowSubgroupInAmbient M P A ∈ scnPrimeSubgroups 3 p G := by
  have hp_dvd_G : p ∣ Nat.card G :=
    (hpF : p ∣ Nat.card (section8FittingSubgroup M)).trans
      (Subgroup.card_subgroup_dvd_card (section8FittingSubgroup M))
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  rcases section8_part_b_sylow_core hM hpF hFp P with ⟨P₀, hP₀eq⟩
  refine ⟨P₀, ?_, ?_⟩
  · intro x hx
    rw [hP₀eq]
    change x ∈ (P : Subgroup M).map M.subtype
    rcases Subgroup.mem_map.mp hx with ⟨y, hyAmap, rfl⟩
    rcases Subgroup.mem_map.mp hyAmap with ⟨a, _haA, rfl⟩
    exact Subgroup.mem_map_of_mem M.subtype a.property
  · have hscn :
        (section8SylowSubgroupInAmbient M P A).subgroupOf
          (section8SubgroupInAmbient (P : Subgroup M)) ∈
            scnSubgroups 3 (section8SubgroupInAmbient (P : Subgroup M)) :=
      section8SylowSubgroupInAmbient_subgroupOf_sylowImage_mem_scnSubgroups hpodd P hA
    change
      (section8SylowSubgroupInAmbient M P A).subgroupOf (P₀ : Subgroup G) ∈
        scnSubgroups 3 (P₀ : Subgroup G)
    rw [hP₀eq]
    exact hscn

/-- In branch (b), Theorem 7.6 and the trivial centralizer `p'`-core make each
`H_G^*(A;q)` family subsingleton for `q ≠ p`. -/
public theorem CFSG.section8_HStarFamily_sylowSubgroupInAmbient_subsingleton_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩) :
    Subsingleton {Q : Subgroup G //
      Q ∈ section7HStarFamily (⊤ : Subgroup G)
        (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes)} := by
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  have hp_dvd_G : p ∣ Nat.card G :=
    (hpF : p ∣ Nat.card (section8FittingSubgroup M)).trans
      (Subgroup.card_subgroup_dvd_card (section8FittingSubgroup M))
  have hAscn : A_G ∈ scnPrimeSubgroups 3 p G := by
    simpa [A_G] using
      section8SylowSubgroupInAmbient_mem_scnPrimeSubgroups_of_fitting_isPGroup
        hM hpF hFp P hA
  have htrans : ConjugationActionTransitiveOn
      (piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ)
        (Subgroup.centralizer (A_G : Set G)))
      (section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes)) :=
    theorem_7_6 (G := G) (p := p) hp_dvd_G hAscn hq
  have hKbot : piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ)
      (Subgroup.centralizer (A_G : Set G)) = ⊥ := by
    simpa [A_G] using
      section8_piCoreIn_centralizer_sylowSubgroupInAmbient_singleton_compl_eq_bot
        hM hpF hFp P hA
  refine ⟨?_⟩
  intro Q₁ Q₂
  apply Subtype.ext
  rcases htrans Q₁ Q₁.property Q₂ Q₂.property with ⟨k, hk⟩
  have hk1 : (k : G) = 1 := by
    have hkbot : (k : G) ∈ (⊥ : Subgroup G) := by
      simpa [hKbot] using k.property
    simpa using hkbot
  have hconj1 : (Q₁ : Subgroup G).conjBy (1 : G) = Q₁ := by
    ext x
    simp [Subgroup.conjBy]
  rw [hk1, hconj1] at hk
  exact hk.symm

/-- Conjugating a subgroup twice composes the conjugating elements. -/
public theorem CFSG.section8_conjBy_conjBy [Finite G] (H : Subgroup G) (g h : G) :
    (H.conjBy g).conjBy h = H.conjBy (h * g) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
    · simp [MulAut.conj_apply, mul_assoc]

/-- Conjugating a subgroup by the identity leaves it unchanged. -/
public theorem CFSG.section8_conjBy_one [Finite G] (H : Subgroup G) :
    H.conjBy (1 : G) = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Subgroup.conjBy, MulAut.conj_apply]
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp⟩

/-- Conjugating a top-level Section 7 family member by an element normalizing `A` keeps it
in the same family. This public Section 8 wrapper mirrors the private Section 7 helper. -/
public theorem CFSG.section8_mem_section7HFamily_top_conjBy_of_mem_normalizer
    [Finite G] {A Q : Subgroup G} {π : Set Nat.Primes} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hQ : Q ∈ section7HFamily (⊤ : Subgroup G) A π) :
    Q.conjBy g ∈ section7HFamily (⊤ : Subgroup G) A π := by
  rcases hQ with ⟨_, hQπ, hAnormQ⟩
  have hg_inv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem hg
  refine ⟨le_top, ?_, ?_⟩
  · intro q hqQ
    have hcard :
        Nat.card (Q.conjBy g) = Nat.card Q := by
      simpa [Subgroup.conjBy] using
        Subgroup.card_map_of_injective
          (K := Q) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    exact hQπ q (by simpa [hcard] using hqQ)
  · refine subgroup_le_normalizer_of_conj_mem (Q.conjBy g) A ?_
    intro a x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hgaA : g⁻¹ * a * g ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp hg_inv (a : G)).1 a.property
    have hy' : (g⁻¹ * a * g) * y * (g⁻¹ * a * g)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hAnormQ hgaA) y).1 hy
    exact Subgroup.mem_map.mpr ⟨_, hy', by simp [mul_assoc]⟩

/-- Conjugating a top-level Section 7 star-family member by an element normalizing `A` keeps
it in the same star family. -/
public theorem CFSG.section8_mem_section7HStarFamily_top_conjBy_of_mem_normalizer
    [Finite G] {A Q : Subgroup G} {π : Set Nat.Primes} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) A π) :
    Q.conjBy g ∈ section7HStarFamily (⊤ : Subgroup G) A π := by
  refine ⟨section8_mem_section7HFamily_top_conjBy_of_mem_normalizer hg hQ.1, ?_⟩
  intro R hQR hR
  have hg_inv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem hg
  have hR_back :
      R.conjBy g⁻¹ ∈ section7HFamily (⊤ : Subgroup G) A π :=
    section8_mem_section7HFamily_top_conjBy_of_mem_normalizer hg_inv hR
  have hQ_le_back : Q ≤ R.conjBy g⁻¹ := by
    intro x hx
    have hxR : g * x * g⁻¹ ∈ R := hQR (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hxR, by simp [mul_assoc]⟩
  have hEq_back : R.conjBy g⁻¹ = Q := hQ.2 _ hQ_le_back hR_back
  calc
    R = (R.conjBy g⁻¹).conjBy g := by
      rw [section8_conjBy_conjBy]
      simpa using (section8_conjBy_one R).symm
    _ = Q.conjBy g := by simp [hEq_back]

/-- Every Section 7 family member is contained in a maximal star-family member. This public
Section 8 wrapper mirrors the private Section 7 helper. -/
public theorem CFSG.section8_exists_mem_section7HStarFamily_of_mem_family
    [Finite G] {H A R : Subgroup G} {π : Set Nat.Primes}
    (hR : R ∈ section7HFamily H A π) :
    ∃ Q ∈ section7HStarFamily H A π, R ≤ Q := by
  let s : Set (Subgroup G) := {Q | R ≤ Q ∧ Q ∈ section7HFamily H A π}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨R, le_rfl, hR⟩
  obtain ⟨Q, hQ, hQmax⟩ := hsfin.exists_maximal hsne
  refine ⟨Q, ?_, hQ.1⟩
  refine ⟨hQ.2, ?_⟩
  intro S hQS hS
  exact le_antisymm (hQmax ⟨hQ.1.trans hQS, hS⟩ hQS) hQS

/-- In branch (b), `F(M)` normalizes every transported `SCN_3(P)` subgroup. -/
public theorem CFSG.section8FittingSubgroup_le_normalizer_sylowSubgroupInAmbient_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    section8FittingSubgroup M ≤
      Subgroup.normalizer (section8SylowSubgroupInAmbient M P A : Set G) := by
  intro f hfF
  have hfPambient : f ∈ section8SubgroupInAmbient (P : Subgroup M) :=
    section8FittingSubgroup_le_sylow hFp P hfF
  rcases Subgroup.mem_map.mp hfPambient with ⟨fM, hfMP, hf_eq⟩
  let fP : (P : Subgroup M) := ⟨fM, hfMP⟩
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hxA
  change f * x * f⁻¹ ∈ ((A.map (P : Subgroup M).subtype).map M.subtype)
  rcases Subgroup.mem_map.mp hxA with ⟨xM, hxAmap, hx_eq⟩
  rcases Subgroup.mem_map.mp hxAmap with ⟨xP, hxA', hxM_eq⟩
  have hx_conj_A : fP * xP * fP⁻¹ ∈ A :=
    hA.1.conj_mem xP hxA' fP
  refine Subgroup.mem_map.mpr ?_
  refine ⟨((fP * xP * fP⁻¹ : (P : Subgroup M)) : M), ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem (P : Subgroup M).subtype hx_conj_A
  · calc
      (((fP * xP * fP⁻¹ : (P : Subgroup M)) : M) : G)
          = (fP : G) * (xP : G) * (fP : G)⁻¹ := rfl
      _ = f * x * f⁻¹ := by
        rw [← hf_eq, ← hx_eq]
        change (fM : G) * ((xP : M) : G) * (fM : G)⁻¹ =
          (fM : G) * (xM : G) * (fM : G)⁻¹
        have hxM_eq_G : ((xP : M) : G) = (xM : G) := congrArg Subtype.val hxM_eq
        rw [hxM_eq_G]

/-- In branch (b), Theorem 7.4 embeds the `H^*` family for `F(M)` into the `H^*`
family for each transported `SCN_3(P)` subgroup. -/
public theorem CFSG.section8_HStarFamily_fitting_subset_sylowSubgroupInAmbient_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩) :
    section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
        ({q} : Set Nat.Primes) ⊆
      section7HStarFamily (⊤ : Subgroup G)
        (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes) := by
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  let F : Subgroup G := section8FittingSubgroup M
  have hp_dvd_G : p ∣ Nat.card G :=
    (hpF : p ∣ Nat.card (section8FittingSubgroup M)).trans
      (Subgroup.card_subgroup_dvd_card (section8FittingSubgroup M))
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hAπ : subgroupPrimeSet A_G = ({⟨p, Fact.out⟩} : Set Nat.Primes) := by
    simpa [A_G] using
      section8_subgroupPrimeSet_sylowSubgroupInAmbient_eq_singleton hpodd P hA
  have hq_not_mem : q ∉ subgroupPrimeSet A_G := by
    rw [hAπ]
    exact fun hmem => hq (Set.mem_singleton_iff.mp hmem)
  have hAp : IsPGroup p A_G := by
    simpa [A_G] using section8SylowSubgroupInAmbient_isPGroup M P A
  have hAcomm0 : IsMulCommutative A :=
    (scnSubgroup_normal_commutative
      (p := p) (R := (P : Subgroup M)) P.isPGroup' hA).2
  have hAMcomm : IsMulCommutative (A.map (P : Subgroup M).subtype) := by
    let : IsMulCommutative A := hAcomm0
    exact Subgroup.map_isMulCommutative (f := (P : Subgroup M).subtype) (H := A)
  have hAcomm : IsMulCommutative A_G := by
    let : IsMulCommutative (A.map (P : Subgroup M).subtype) := hAMcomm
    change IsMulCommutative ((A.map (P : Subgroup M).subtype).map M.subtype)
    exact
      Subgroup.map_isMulCommutative
        (f := M.subtype) (H := A.map (P : Subgroup M).subtype)
  have hAscn3 : A_G ∈ scnPrimeSubgroups 3 p G := by
    simpa [A_G] using
      section8SylowSubgroupInAmbient_mem_scnPrimeSubgroups_of_fitting_isPGroup
        hM hpF hFp P hA
  have hAscn2 : A_G ∈ scnPrimeSubgroups 2 p G := by
    rcases hAscn3 with ⟨P₀, hA_le_P₀, hA₀⟩
    exact ⟨P₀, hA_le_P₀, ⟨hA₀.1, hA₀.2.1, (by decide : 2 ≤ 3).trans hA₀.2.2⟩⟩
  let : IsMulCommutative A_G := hAcomm
  have hHyp : Hypothesis7_1 A_G :=
    proposition_7_5 (G := G) (p := p) hp_dvd_G hAp (Or.inr hAscn2)
  have htrans : ConjugationActionTransitiveOn (section7K A_G)
      (section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes)) := by
    simpa [section7K, hAπ] using
      theorem_7_6 (G := G) (p := p) hp_dvd_G hAscn3 hq
  have hAF : A_G ≤ F := by
    simpa [A_G, F] using
      section8SylowSubgroupInAmbient_le_fitting_of_isPGroup hM hFp P hA
  have hF_ne_top : F ≠ ⊤ := by
    simpa [F] using section8_ne_top_of_le_maximal hM (section8FittingSubgroup_le M)
  have hFnormA : F ≤ Subgroup.normalizer (A_G : Set G) := by
    simpa [A_G, F] using
      section8FittingSubgroup_le_normalizer_sylowSubgroupInAmbient_of_fitting_isPGroup
        hFp P hA
  have hAnormF : (A_G.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAF).mpr hFnormA
  let : (A_G.subgroupOf F).Normal := hAnormF
  have hAsubnormal : IsSubnormalIn A_G F :=
    section8_isSubnormalIn_of_normal_subgroupOf hAF
  have hFπ : IsPiSubgroup (G := G) (subgroupPrimeSet A_G) F := by
    intro r hrF
    have hr_eq_p : r = ⟨p, Fact.out⟩ := by
      have hr_not_ne : ¬ r ≠ ⟨p, Fact.out⟩ := by
        intro hrne
        exact section8_not_mem_subgroupPrimeSet_of_isPGroup_ne hFp hrne hrF
      exact not_not.mp hr_not_ne
    simp [hAπ, hr_eq_p]
    exact Set.mem_singleton_iff.mpr rfl
  have hres :=
    theorem_7_4 (G := G) (A := A_G) (P := F)
      hHyp hq_not_mem hF_ne_top hAsubnormal hFπ htrans
  exact hres.2.2.1

/-- A subgroup whose prime support is contained in a singleton is a `q`-group. -/
public lemma CFSG.section8_isPGroup_of_isPiSubgroup_singleton
    [Finite G] {H : Subgroup G} {q : Nat.Primes}
    (hH : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) H) :
    IsPGroup q.val H := by
  let : Fact q.val.Prime := ⟨q.2⟩
  rw [IsPGroup.iff_card]
  have hcard_ne_zero : Nat.card H ≠ 0 := Nat.card_pos.ne'
  refine ⟨(Nat.card H).primeFactorsList.length, ?_⟩
  rw [← List.prod_replicate, ← List.eq_replicate_of_mem ?_, Nat.prod_primeFactorsList hcard_ne_zero]
  intro p hp
  obtain ⟨hp_prime, hp_dvd⟩ := (Nat.mem_primeFactorsList hcard_ne_zero).mp hp
  let p' : Nat.Primes := ⟨p, hp_prime⟩
  have hp_mem : p' ∈ ({q} : Set Nat.Primes) := hH p' hp_dvd
  simpa [p'] using congrArg Subtype.val hp_mem

/-- A finite `q`-group is a singleton-prime `π`-subgroup. -/
public lemma CFSG.section8_isPiSubgroup_singleton_of_isPGroup
    [Finite G] {H : Subgroup G} {q : Nat.Primes}
    (hH : IsPGroup q.val H) :
    IsPiSubgroup (G := G) ({q} : Set Nat.Primes) H := by
  let : Fact q.val.Prime := ⟨q.2⟩
  intro r hr
  obtain ⟨n, hncard⟩ := hH.exists_card_eq
  have hrdvdq : r.val ∣ q.val := r.2.dvd_of_dvd_pow (by simpa [hncard] using hr)
  have hr_eq_q : r = q :=
    Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hrdvdq)
  simp [hr_eq_q]

/-- An `r`-group and a `πᶜ`-subgroup have coprime orders when `r ∈ π`. -/
public theorem CFSG.section8_coprime_card_of_isPGroup_of_isPiSubgroup_compl
    [Finite G] {π : Set Nat.Primes} {r : Nat.Primes} {R Y : Subgroup G}
    (hrπ : r ∈ π) (hR : IsPGroup r.val R)
    (hY : IsPiSubgroup (G := G) πᶜ Y) :
    Nat.Coprime (Nat.card R) (Nat.card Y) := by
  let : Fact r.val.Prime := ⟨r.2⟩
  refine Nat.coprime_of_dvd ?_
  intro l hlprime hlR hlY
  let l' : Nat.Primes := ⟨l, hlprime⟩
  have hl_eq_r : l' = r := by
    by_contra hlne
    exact section8_not_mem_subgroupPrimeSet_of_isPGroup_ne
      (p := r.val) (H := R) hR hlne hlR
  have hl_notπ : l' ∉ π := by
    simpa using hY l' hlY
  exact hl_notπ (by simpa [hl_eq_r] using hrπ)

/-- A subgroup contained in both a `π`-subgroup and a `πᶜ`-subgroup is trivial. -/
public theorem CFSG.section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
    [Finite G] {π : Set Nat.Primes} {H Y C : Subgroup G}
    (hHY : H ≤ Y) (hHC : H ≤ C)
    (hY : IsPiSubgroup (G := G) πᶜ Y)
    (hC : IsPiSubgroup (G := G) π C) :
    H = ⊥ := by
  by_contra hH_ne_bot
  have hcard_ne_one : Nat.card H ≠ 1 := by
    intro hcard
    exact hH_ne_bot ((Subgroup.card_eq_one (H := H)).1 hcard)
  obtain ⟨l, hlprime, hlH⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let l' : Nat.Primes := ⟨l, hlprime⟩
  have hlY : l' ∈ πᶜ :=
    hY l' (hlH.trans (Subgroup.card_dvd_of_le hHY))
  have hlC : l' ∈ π :=
    hC l' (hlH.trans (Subgroup.card_dvd_of_le hHC))
  exact hlY hlC

/-- If a finite subgroup has `p` in its prime support but is not a `p`-group, then
its prime support contains a prime different from `p`. -/
public theorem CFSG.section8_exists_prime_ne_of_not_isPGroup
    [Finite G] {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hnot : ¬ IsPGroup p H) :
    ∃ q : Nat.Primes, q ∈ subgroupPrimeSet H ∧ q ≠ ⟨p, Fact.out⟩ := by
  by_contra hnone
  have hsubset : subgroupPrimeSet H ⊆ ({⟨p, Fact.out⟩} : Set Nat.Primes) := by
    intro q hqH
    by_contra hqnot
    exact hnone ⟨q, hqH, fun heq => hqnot (Set.mem_singleton_iff.mpr heq)⟩
  have hHπ : IsPiSubgroup (G := G) ({⟨p, Fact.out⟩} : Set Nat.Primes) H :=
    section8_isPiSubgroup_of_subgroupPrimeSet_subset hsubset
  exact hnot (section8_isPGroup_of_isPiSubgroup_singleton hHπ)

/-- In the non-`p` branch of Section 8, `π(C_{F(M)}(A₀))` contains a prime different
from `p`. -/
public theorem CFSG.section8CentralizerInFitting_exists_prime_ne_of_not_isPGroup
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    (A₀ : Subgroup (section8FittingSubgroup M)) :
    ∃ q : Nat.Primes,
      q ∈ subgroupPrimeSet (section8CentralizerInFitting M A₀) ∧
        q ≠ ⟨p, Fact.out⟩ := by
  rcases section8_exists_prime_ne_of_not_isPGroup hnFp with ⟨q, hqF, hqne⟩
  refine ⟨q, ?_, hqne⟩
  have hπeq :
      subgroupPrimeSet (section8CentralizerInFitting M A₀) =
        subgroupPrimeSet (section8FittingSubgroup M) :=
    section8CentralizerInFitting_primeSet_eq_fitting M A₀
  rw [hπeq]
  exact hqF

/-- In a commutative subgroup, a prime divisor gives a nontrivial singleton `π`-core. -/
public theorem CFSG.section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isMulCommutative
    [Finite G] {H : Subgroup G} [IsMulCommutative H] {q : Nat.Primes}
    (hqH : q ∈ subgroupPrimeSet H) :
    piCoreIn ({q} : Set Nat.Primes) H ≠ ⊥ := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let Q : Sylow q.val H := default
  have hq_card_H : q.val ∣ Nat.card H := hqH
  have hQ_ne_bot : (Q : Subgroup H) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card Q hq_card_H
  have hQ_norm : (Q : Subgroup H).Normal := by infer_instance
  have hQ_pi : IsPiSubgroup (G := H) ({q} : Set Nat.Primes) (Q : Subgroup H) :=
    section8_isPiSubgroup_singleton_of_isPGroup Q.isPGroup'
  have hQ_le_core : (Q : Subgroup H) ≤ piCore ({q} : Set Nat.Primes) H :=
    le_sSup
      (show (Q : Subgroup H) ∈
          {K : Subgroup H | K.Normal ∧
            IsPiSubgroup (G := H) ({q} : Set Nat.Primes) K} from
        ⟨hQ_norm, hQ_pi⟩)
  intro hbot
  have hcore_bot : piCore ({q} : Set Nat.Primes) H = ⊥ := by
    apply Subgroup.map_injective H.subtype_injective
    simpa [piCoreIn] using hbot
  exact hQ_ne_bot (le_bot_iff.mp (hQ_le_core.trans (le_of_eq hcore_bot)))

/-- In a finite nilpotent subgroup, a prime divisor gives a nontrivial singleton
`π`-core. -/
public theorem CFSG.section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isNilpotent
    [Finite G] {H : Subgroup G} [Group.IsNilpotent H] {q : Nat.Primes}
    (hqH : q ∈ subgroupPrimeSet H) :
    piCoreIn ({q} : Set Nat.Primes) H ≠ ⊥ := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let Q : Sylow q.val H := default
  have hq_card_H : q.val ∣ Nat.card H := hqH
  have hQ_ne_bot : (Q : Subgroup H) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card Q hq_card_H
  have hQ_norm : (Q : Subgroup H).Normal :=
    Group.IsNilpotent.sylow_normal (show Group.IsNilpotent H from inferInstance) q.val Q
  have hQ_pi : IsPiSubgroup (G := H) ({q} : Set Nat.Primes) (Q : Subgroup H) :=
    section8_isPiSubgroup_singleton_of_isPGroup Q.isPGroup'
  have hQ_le_core : (Q : Subgroup H) ≤ piCore ({q} : Set Nat.Primes) H :=
    le_sSup
      (show (Q : Subgroup H) ∈
          {K : Subgroup H | K.Normal ∧
            IsPiSubgroup (G := H) ({q} : Set Nat.Primes) K} from
        ⟨hQ_norm, hQ_pi⟩)
  intro hbot
  have hcore_bot : piCore ({q} : Set Nat.Primes) H = ⊥ := by
    apply Subgroup.map_injective H.subtype_injective
    simpa [piCoreIn] using hbot
  exact hQ_ne_bot (le_bot_iff.mp (hQ_le_core.trans (le_of_eq hcore_bot)))

/-- For a singleton, `piCoreIn` is the transported `pCore`. -/
public theorem CFSG.section8_piCoreIn_singleton_eq_pCore_map
    [Finite G] (q : Nat.Primes) (H : Subgroup G) :
    piCoreIn ({q} : Set Nat.Primes) H = (pCore q.val H).map H.subtype := by
  let : Fact q.val.Prime := ⟨q.2⟩
  let Sπ : Set (Subgroup H) :=
    {K | K.Normal ∧ IsPiSubgroup (G := H) ({q} : Set Nat.Primes) K}
  let Sq : Set (Subgroup H) := {K | K.Normal ∧ IsPGroup q.val K}
  have hsets : Sπ = Sq := by
    ext K
    constructor
    · rintro ⟨hKnorm, hKπ⟩
      exact ⟨hKnorm, section8_isPGroup_of_isPiSubgroup_singleton hKπ⟩
    · rintro ⟨hKnorm, hKq⟩
      exact ⟨hKnorm, section8_isPiSubgroup_singleton_of_isPGroup hKq⟩
  calc
    piCoreIn ({q} : Set Nat.Primes) H
        = (piCore ({q} : Set Nat.Primes) H).map H.subtype := rfl
    _ = (sSup Sπ).map H.subtype := rfl
    _ = (sSup Sq).map H.subtype := by rw [hsets]
    _ = (pCore q.val H).map H.subtype := rfl

/-- If `Y <= X` lies in every singleton complement `π`-core of `X` for primes in `π`,
then `Y` lies in the full `πᶜ`-core of `X`. -/
public theorem CFSG.section8_le_piCoreIn_compl_of_forall_le_singleton_compl
    [Finite G] {π : Set Nat.Primes} {X Y : Subgroup G} (hYX : Y ≤ X)
    (hYq : ∀ q : Nat.Primes, q ∈ π →
      Y ≤ piCoreIn ({q} : Set Nat.Primes)ᶜ X) :
    Y ≤ piCoreIn πᶜ X := by
  classical
  let L : Subgroup X :=
    ⨅ q : {q : Nat.Primes // q ∈ π},
      piCore ({(q : Nat.Primes)} : Set Nat.Primes)ᶜ X
  have hLnorm : L.Normal := by
    simpa [L] using
      Subgroup.normal_iInf_normal (fun q : {q : Nat.Primes // q ∈ π} =>
        (inferInstance :
          (piCore ({(q : Nat.Primes)} : Set Nat.Primes)ᶜ X).Normal))
  have hLπ : IsPiSubgroup (G := X) πᶜ L := by
    intro r hrL
    rw [Set.mem_compl_iff]
    intro hrπ
    let qr : {q : Nat.Primes // q ∈ π} := ⟨r, hrπ⟩
    have hL_le_r : L ≤ piCore ({r} : Set Nat.Primes)ᶜ X := by
      change L ≤ (fun q : {q : Nat.Primes // q ∈ π} =>
        piCore ({(q : Nat.Primes)} : Set Nat.Primes)ᶜ X) qr
      exact iInf_le _ qr
    have hrdvd :
        r.val ∣ Nat.card (piCore ({r} : Set Nat.Primes)ᶜ X) :=
      hrL.trans (Subgroup.card_dvd_of_le hL_le_r)
    have hrmem_compl : r ∈ ({r} : Set Nat.Primes)ᶜ :=
      piCore_isPiSubgroup (G := X) ({r} : Set Nat.Primes)ᶜ r hrdvd
    exact hrmem_compl (Set.mem_singleton r)
  have hL_le_core : L ≤ piCore πᶜ X :=
    le_sSup (show L ∈ {K : Subgroup X | K.Normal ∧ IsPiSubgroup (G := X) πᶜ K} from
      ⟨hLnorm, hLπ⟩)
  have hY_le_Lmap : Y ≤ L.map X.subtype := by
    intro y hyY
    let yX : X := ⟨y, hYX hyY⟩
    have hyL : yX ∈ L := by
      simp only [L, Subgroup.mem_iInf]
      intro q
      have hyqG : y ∈ piCoreIn ({(q : Nat.Primes)} : Set Nat.Primes)ᶜ X :=
        hYq q q.property hyY
      have hyqSub :
          yX ∈ (piCoreIn ({(q : Nat.Primes)} : Set Nat.Primes)ᶜ X).subgroupOf X := by
        change y ∈ piCoreIn ({(q : Nat.Primes)} : Set Nat.Primes)ᶜ X
        exact hyqG
      simpa [piCore_map_subtype_subgroupOf] using hyqSub
    exact Subgroup.mem_map.mpr ⟨yX, hyL, rfl⟩
  exact hY_le_Lmap.trans (by
    simpa [piCoreIn] using Subgroup.map_mono (f := X.subtype) hL_le_core)

/-- Normalizing a subgroup also normalizes its transported `π`-core. -/
public theorem CFSG.section8_le_normalizer_piCoreIn_of_le_normalizer
    [Finite G] {π : Set Nat.Primes} {H P : Subgroup G}
    (hPH : P ≤ Subgroup.normalizer (H : Set G)) :
    P ≤ Subgroup.normalizer (piCoreIn π H : Set G) := by
  have hpi_le_H : piCoreIn π H ≤ H := piCoreIn_le (G := G) π H
  have hsub_eq : (piCoreIn π H).subgroupOf H = piCore π ↥H := by
    simpa using piCore_map_subtype_subgroupOf (G := G) π H
  have hsub_char : ((piCoreIn π H).subgroupOf H).Characteristic := by
    rw [hsub_eq]
    exact piCore_characteristic (G := ↥H) π
  refine subgroup_le_normalizer_of_conj_mem (piCoreIn π H) P ?_
  intro p x hx
  let pH : Subgroup.normalizer (H : Set G) := ⟨p, hPH p.property⟩
  let xH : H := ⟨x, hpi_le_H hx⟩
  have hxH : xH ∈ (piCoreIn π H).subgroupOf H := by
    change x ∈ piCoreIn π H
    exact hx
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H pH).toMonoidHom
          ((piCoreIn π H).subgroupOf H) =
        (piCoreIn π H).subgroupOf H :=
    hsub_char.fixed (Subgroup.normalizerMonoidHom H pH)
  have hxComap :
      xH ∈
        Subgroup.comap (Subgroup.normalizerMonoidHom H pH).toMonoidHom
          ((piCoreIn π H).subgroupOf H) := by
    rw [hfix]
    exact hxH
  have hxImage :
      (Subgroup.normalizerMonoidHom H pH) xH ∈ (piCoreIn π H).subgroupOf H :=
    hxComap
  change (p : G) * x * (p : G)⁻¹ ∈ piCoreIn π H at hxImage
  simpa [pH, xH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe] using hxImage

/-- Coprime-action generation in ambient subgroup notation: if `R` normalizes `Y` and
has no fixed points on `Y`, then `Y <= [Y,R]`. -/
public theorem CFSG.section8_le_commutator_of_subgroupCentralizerIn_eq_bot
    [Finite G] {Y R : Subgroup G} (hsolvY : Group.IsSolvable Y)
    (hRYnorm : R ≤ Subgroup.normalizer (Y : Set G))
    (hcop : Nat.Coprime (Nat.card R) (Nat.card Y))
    (hfix : subgroupCentralizerIn Y R = ⊥) :
    Y ≤ ⁅Y, R⁆ := by
  classical
  have : Subgroup.Normalizes R Y := ⟨hRYnorm⟩
  have hfixed_eq :
      fixedPointSubgroup (↥R) (↥Y) = (subgroupCentralizerIn Y R).subgroupOf Y := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Y R hRYnorm
  have hfixed_bot : fixedPointSubgroup (↥R) (↥Y) = ⊥ := by
    rw [hfixed_eq, hfix]
    ext y
    simp
  have hsup :
      fixedPointSubgroup (↥R) (↥Y) ⊔ commutatorAction (A := ↥R) (G := ↥Y) = ⊤ :=
    proposition_1_6_a (G := Y) (A := R) hsolvY hcop
  have hcomm_top : commutatorAction (A := ↥R) (G := ↥Y) = ⊤ := by
    simpa [hfixed_bot] using hsup
  have hcomm_map :
      (commutatorAction (A := ↥R) (G := ↥Y)).map Y.subtype = ⁅Y, R⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator Y R hRYnorm
  intro y hyY
  let yY : Y := ⟨y, hyY⟩
  have hyComm : yY ∈ commutatorAction (A := ↥R) (G := ↥Y) := by
    rw [hcomm_top]
    exact Subgroup.mem_top yY
  have hyMap : y ∈ (commutatorAction (A := ↥R) (G := ↥Y)).map Y.subtype :=
    Subgroup.mem_map.mpr ⟨yY, hyComm, rfl⟩
  simpa [hcomm_map] using hyMap

/-- If the right-hand subgroup of a commutator lies in the transported `π`-core of `X`
and the left-hand subgroup lies in `X`, then the commutator lies in that core. -/
public theorem CFSG.section8_commutator_le_piCoreIn_of_right_le
    [Finite G] {π : Set Nat.Primes} {X Y R : Subgroup G}
    (hYX : Y ≤ X) (hRcore : R ≤ piCoreIn π X) :
    ⁅Y, R⁆ ≤ piCoreIn π X := by
  let K : Subgroup G := piCoreIn π X
  have hKX : K ≤ X := by
    simpa [K] using piCoreIn_le (G := G) π X
  have hRX : R ≤ X := hRcore.trans hKX
  have hKsub_norm : (K.subgroupOf X).Normal := by
    have hsub_eq : K.subgroupOf X = piCore π X := by
      simpa [K] using piCore_map_subtype_subgroupOf (G := G) π X
    rw [hsub_eq]
    infer_instance
  have hRsub_le_Ksub : R.subgroupOf X ≤ K.subgroupOf X := by
    intro x hx
    exact hRcore hx
  have hcomm_sub_le :
      ⁅Y.subgroupOf X, R.subgroupOf X⁆ ≤ K.subgroupOf X := by
    have hmono :
        ⁅Y.subgroupOf X, R.subgroupOf X⁆ ≤ ⁅Y.subgroupOf X, K.subgroupOf X⁆ :=
      Subgroup.commutator_mono le_rfl hRsub_le_Ksub
    exact hmono.trans (Subgroup.commutator_le_right (Y.subgroupOf X) (K.subgroupOf X))
  intro z hz
  have hzmap :
      z ∈ (⁅Y.subgroupOf X, R.subgroupOf X⁆).map X.subtype := by
    rw [commutator_subgroupOf_map_eq X R Y hRX hYX]
    exact hz
  rcases Subgroup.mem_map.mp hzmap with ⟨x, hx, rfl⟩
  change (x : G) ∈ K
  exact hcomm_sub_le hx

/-- A prime different from the defining prime of a finite `r`-group is coprime to its
order. -/
public theorem CFSG.section8_coprime_prime_card_of_isPGroup_ne
    [Finite G] {R : Subgroup G} {q r : Nat.Primes}
    (hqr : q ≠ r) (hR : IsPGroup r.val R) :
    Nat.Coprime q.val (Nat.card R) := by
  let : Fact r.val.Prime := ⟨r.2⟩
  have hr_cast : (⟨r.val, Fact.out⟩ : Nat.Primes) = r := Subtype.ext rfl
  have hnot : ¬ q.val ∣ Nat.card R := by
    intro hq
    have hq_ne : q ≠ (⟨r.val, Fact.out⟩ : Nat.Primes) := by
      intro h
      exact hqr (h.trans hr_cast)
    exact section8_not_mem_subgroupPrimeSet_of_isPGroup_ne
      (p := r.val) (H := R) hR hq_ne hq
  exact q.2.coprime_iff_not_dvd.mpr hnot

/-- If `A ≤ F(M)`, then the ambient commutator `[M,A]` lies in `F(M)`. -/
public theorem CFSG.section8_commutator_maximal_le_fitting_of_le_fitting
    [Finite G] (M : Subgroup G) {A : Subgroup G}
    (hAF : A ≤ section8FittingSubgroup M) :
    ⁅M, A⁆ ≤ section8FittingSubgroup M := by
  let F : Subgroup G := section8FittingSubgroup M
  have hAM : A ≤ M := hAF.trans (section8FittingSubgroup_le M)
  let Fsub : Subgroup M := F.subgroupOf M
  have hFsub_norm : Fsub.Normal := by
    simpa [F, Fsub] using section8FittingSubgroup_normal_in M
  have hAsub_le_Fsub : A.subgroupOf M ≤ Fsub := by
    intro x hx
    exact hAF hx
  have hMsub_top : M.subgroupOf M = ⊤ := by
    ext x
    simp
  have hcomm_sub_le :
      ⁅M.subgroupOf M, A.subgroupOf M⁆ ≤ Fsub := by
    rw [hMsub_top]
    have hmono :
        ⁅(⊤ : Subgroup M), A.subgroupOf M⁆ ≤ ⁅(⊤ : Subgroup M), Fsub⁆ :=
      Subgroup.commutator_mono le_rfl hAsub_le_Fsub
    exact hmono.trans (Subgroup.commutator_le_right (⊤ : Subgroup M) Fsub)
  intro z hz
  have hzmap :
      z ∈ (⁅M.subgroupOf M, A.subgroupOf M⁆).map M.subtype := by
    rw [commutator_subgroupOf_map_eq M A M hAM le_rfl]
    exact hz
  rcases Subgroup.mem_map.mp hzmap with ⟨x, hx, rfl⟩
  change (x : G) ∈ F
  exact hcomm_sub_le hx

/-- The singleton `π`-core of `Z(F(M))` is an `q`-group. -/
public theorem CFSG.section8_piCoreIn_singleton_centerInFitting_isPGroup
    [Finite G] (M : Subgroup G) (q : Nat.Primes) :
    IsPGroup q.val (piCoreIn ({q} : Set Nat.Primes) (section8CenterInFitting M)) := by
  exact
    section8_isPGroup_of_isPiSubgroup_singleton
      (piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes) (section8CenterInFitting M))

/-- Equation (8.2) normalizer component:
`N_G(O_q(Z(F(M)))) = M` for `q ∈ π(F(M))`, using the singleton `π`-core notation. -/
public theorem CFSG.section8_normalizer_piCoreIn_singleton_centerInFitting_eq
    [Finite G] [IsMinCE G] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {q : Nat.Primes} (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M)) :
    Subgroup.normalizer
        (piCoreIn ({q} : Set Nat.Primes) (section8CenterInFitting M) : Set G) = M := by
  let Z : Subgroup G := section8CenterInFitting M
  let L : Subgroup G := piCoreIn ({q} : Set Nat.Primes) Z
  have hπZ : subgroupPrimeSet Z = subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [Z] using section8CenterInFitting_primeSet_eq_fitting M
  have hqZ : q ∈ subgroupPrimeSet Z := by
    rw [hπZ]
    exact hqF
  have hZcomm : IsMulCommutative Z := by
    simpa [Z] using section8CenterInFitting_isMulCommutative M
  let : IsMulCommutative Z := hZcomm
  have hL_ne_bot : L ≠ ⊥ := by
    simpa [L] using
      section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isMulCommutative
        (H := Z) hqZ
  have hL_le_M : L ≤ M :=
    (piCoreIn_le (G := G) ({q} : Set Nat.Primes) Z).trans
      (section8CenterInFitting_le_maximal M)
  have hM_normZ : M ≤ Subgroup.normalizer (Z : Set G) := by
    let : (Z.subgroupOf M).Normal := by
      simpa [Z] using section8CenterInFitting_normal_in_maximal M
    exact
      Subgroup.le_normalizer_of_normal_subgroupOf
        (by simpa [Z] using section8CenterInFitting_le_maximal M)
  have hM_normL : M ≤ Subgroup.normalizer (L : Set G) := by
    simpa [L] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({q} : Set Nat.Primes)) (H := Z) (P := M) hM_normZ
  have hL_norm_M : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL_le_M).mpr hM_normL
  exact section8_normalizer_eq_of_nontrivial_normal_in_maximal hM hL_le_M hL_ne_bot hL_norm_M

/-- The singleton `π`-core of `Z(F(M))` is contained in `C_{F(M)}(A₀)`. -/
public theorem CFSG.section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting
    [Finite G] (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M))
    (q : Nat.Primes) :
    piCoreIn ({q} : Set Nat.Primes) (section8CenterInFitting M) ≤
      section8CentralizerInFitting M A₀ :=
  (piCoreIn_le (G := G) ({q} : Set Nat.Primes) (section8CenterInFitting M)).trans
    (section8CenterInFitting_le_centralizerInFitting M A₀)

/-- Equation (8.5) core containment for the center of `F(M)`: if `q ≠ r` are both in
`π(F(M))`, then the `r`-part of `Z(F(M))` lies in `O_{q'}(X)` for every proper
overgroup `X` of `C_{F(M)}(A₀)`. -/
public theorem CFSG.section8_piCoreIn_singleton_centerInFitting_le_singleton_compl_core
    [Finite G] [IsMinCE G] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (A₀ : Subgroup (section8FittingSubgroup M))
    {X : Subgroup G}
    (hAX : section8CentralizerInFitting M A₀ ≤ X) (hXproper : X ≠ ⊤)
    {q r : Nat.Primes}
    (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hrq : r ≠ q) :
    piCoreIn ({r} : Set Nat.Primes) (section8CenterInFitting M) ≤
      piCoreIn ({q} : Set Nat.Primes)ᶜ X := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let Z : Subgroup G := section8CenterInFitting M
  let Rq : Subgroup G := piCoreIn ({q} : Set Nat.Primes) Z
  let Rr : Subgroup G := piCoreIn ({r} : Set Nat.Primes) Z
  have hRq_le_A : Rq ≤ section8CentralizerInFitting M A₀ := by
    simpa [Rq, Z] using
      section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ q
  have hRr_le_A : Rr ≤ section8CentralizerInFitting M A₀ := by
    simpa [Rr, Z] using
      section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ r
  have hRq_le_X : Rq ≤ X := hRq_le_A.trans hAX
  have hRr_le_X : Rr ≤ X := hRr_le_A.trans hAX
  let C : Subgroup X := Subgroup.centralizer ((Rq.subgroupOf X) : Set X)
  have hRq_p : IsPGroup q.val Rq := by
    simpa [Rq, Z] using section8_piCoreIn_singleton_centerInFitting_isPGroup M q
  have hRqX_p : IsPGroup q.val (Rq.subgroupOf X) :=
    hRq_p.of_equiv (Subgroup.subgroupOfEquivOfLe hRq_le_X).symm
  have hsolvX : Group.IsSolvable X :=
    IsMinCE.proper_subgroups_solvable X (lt_top_iff_ne_top.mpr hXproper)
  have hcoreC_le_coreX :
      (pPrimeCore q.val C).map C.subtype ≤ pPrimeCore q.val X := by
    simpa [C] using
      (proposition_1_15_b (G := X) hsolvX q.val (Rq.subgroupOf X) hRqX_p)
  let : IsMulCommutative Z := by
    simpa [Z] using section8CenterInFitting_isMulCommutative M
  have hRrX_le_C : Rr.subgroupOf X ≤ C := by
    intro x hxRr
    rw [Subgroup.mem_centralizer_iff]
    intro z hzRq
    apply Subtype.ext
    have hxZ : (x : G) ∈ Z :=
      piCoreIn_le (G := G) ({r} : Set Nat.Primes) Z hxRr
    have hzZ : (z : G) ∈ Z :=
      piCoreIn_le (G := G) ({q} : Set Nat.Primes) Z (by
        simpa [Subgroup.mem_subgroupOf] using hzRq)
    exact setLike_mul_comm (s := Z) hzZ hxZ
  have hnormRq_eq : Subgroup.normalizer (Rq : Set G) = M := by
    simpa [Rq, Z] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hqF
  have hC_le_M : ∀ c : X, c ∈ C → (c : G) ∈ M := by
    intro c hc
    have hc_norm : (c : G) ∈ Subgroup.normalizer (Rq : Set G) := by
      refine Subgroup.mem_normalizer_fintype ?_
      intro z hzRq
      have hzX : z ∈ X := hRq_le_X hzRq
      let zX : X := ⟨z, hzX⟩
      have hzRqX : zX ∈ Rq.subgroupOf X := by
        simpa [zX, Subgroup.mem_subgroupOf] using hzRq
      have hcommX := Subgroup.mem_centralizer_iff.mp hc zX hzRqX
      have hcommG : z * (c : G) = (c : G) * z := congrArg Subtype.val hcommX
      have hconj : (c : G) * z * (c : G)⁻¹ = z := by
        calc
          (c : G) * z * (c : G)⁻¹ = (z * (c : G)) * (c : G)⁻¹ := by
            rw [← hcommG]
          _ = z := by simp [mul_assoc]
      simpa [hconj] using hzRq
    simpa [hnormRq_eq] using hc_norm
  have hnormRr_eq : Subgroup.normalizer (Rr : Set G) = M := by
    simpa [Rr, Z] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hrF
  have hC_norm_RrX : C ≤ Subgroup.normalizer ((Rr.subgroupOf X : Subgroup X) : Set X) := by
    intro c hc
    have hcNormG : (c : G) ∈ Subgroup.normalizer (Rr : Set G) := by
      simpa [hnormRr_eq] using hC_le_M c hc
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hyRr
    have hyRrG : (y : G) ∈ Rr := by
      simpa [Subgroup.mem_subgroupOf] using hyRr
    have hconjG : (c : G) * (y : G) * (c : G)⁻¹ ∈ Rr :=
      (Subgroup.mem_normalizer_iff.mp hcNormG (y : G)).1 hyRrG
    change ((c * y * c⁻¹ : X) : G) ∈ Rr
    simpa using hconjG
  have hRrX_norm_C : ((Rr.subgroupOf X).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRrX_le_C).mpr hC_norm_RrX
  have hRr_p : IsPGroup r.val Rr := by
    simpa [Rr, Z] using section8_piCoreIn_singleton_centerInFitting_isPGroup M r
  have hcard_RrXC :
      Nat.card ((Rr.subgroupOf X).subgroupOf C) = Nat.card Rr := by
    calc
      Nat.card ((Rr.subgroupOf X).subgroupOf C) = Nat.card (Rr.subgroupOf X) :=
        natCard_subgroupOf_eq (Rr.subgroupOf X) C hRrX_le_C
      _ = Nat.card Rr :=
        natCard_subgroupOf_eq Rr X hRr_le_X
  have hcopRr : Nat.Coprime q.val (Nat.card Rr) :=
    section8_coprime_prime_card_of_isPGroup_ne
      (G := G) (R := Rr) (q := q) (r := r) (by
        intro hqr
        exact hrq hqr.symm) hRr_p
  have hcopRrC : Nat.Coprime q.val (Nat.card ((Rr.subgroupOf X).subgroupOf C)) := by
    simpa [hcard_RrXC] using hcopRr
  have hRrC_le_core : (Rr.subgroupOf X).subgroupOf C ≤ pPrimeCore q.val C :=
    le_sSup
      (show (Rr.subgroupOf X).subgroupOf C ∈
          {K : Subgroup C | K.Normal ∧ Nat.Coprime q.val (Nat.card K)} from
        ⟨hRrX_norm_C, hcopRrC⟩)
  intro x hxRr
  let xX : X := ⟨x, hRr_le_X hxRr⟩
  have hxC : xX ∈ C := hRrX_le_C (by simpa [xX, Subgroup.mem_subgroupOf] using hxRr)
  let xC : C := ⟨xX, hxC⟩
  have hxCoreC : xC ∈ pPrimeCore q.val C := by
    exact hRrC_le_core (by simpa [xC, xX, Subgroup.mem_subgroupOf] using hxRr)
  have hxCoreX : (xC : X) ∈ pPrimeCore q.val X :=
    hcoreC_le_coreX (Subgroup.mem_map_of_mem C.subtype hxCoreC)
  have hxCoreG : x ∈ (pPrimeCore q.val X).map X.subtype :=
    Subgroup.mem_map.mpr ⟨(xC : X), hxCoreX, rfl⟩
  have hq_cast : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := Subtype.ext rfl
  have hsingleton :
      ({q} : Set Nat.Primes) =
        ({(⟨q.val, Fact.out⟩ : Nat.Primes)} : Set Nat.Primes) := by
    exact congrArg (fun t : Nat.Primes => ({t} : Set Nat.Primes)) hq_cast.symm
  rw [hsingleton]
  have hcore_eq :=
    section8_piCoreIn_singleton_compl_eq_pPrimeCore_map (G := G) (p := q.val) X
  exact (hcore_eq.symm ▸ hxCoreG)

/-- Equation (8.2) consequence: `C_G(C_{F(M)}(A₀)) ≤ M`. -/
public theorem CFSG.section8_centralizer_centralizerInFitting_le_maximal
    [Finite G] [IsMinCE G] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {q : Nat.Primes} (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (A₀ : Subgroup (section8FittingSubgroup M)) :
    Subgroup.centralizer (section8CentralizerInFitting M A₀ : Set G) ≤ M := by
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let L : Subgroup G := piCoreIn ({q} : Set Nat.Primes) (section8CenterInFitting M)
  have hL_le_A : L ≤ A := by
    simpa [L, A] using
      section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ q
  have hnormL_eq : Subgroup.normalizer (L : Set G) = M := by
    simpa [L] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hqF
  intro x hx
  have hx_normL : x ∈ Subgroup.normalizer (L : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hyL
    have hyA : y ∈ A := hL_le_A hyL
    have hcomm := Subgroup.mem_centralizer_iff.mp hx y hyA
    have hconj : x * y * x⁻¹ = y := by
      rw [← hcomm]
      simp [mul_assoc]
    simpa [hconj] using hyL
  simpa [hnormL_eq] using hx_normL

/-- The subgroup `C_{F(M)}(A₀)` is self-centralizing inside `F(M)`: centralizing
`C_{F(M)}(A₀)` in `F(M)` forces centralizing `A₀`. -/
public theorem CFSG.section8_subgroupCentralizerIn_fitting_centralizerInFitting_le
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M)) :
    subgroupCentralizerIn (section8FittingSubgroup M) (section8CentralizerInFitting M A₀) ≤
      section8CentralizerInFitting M A₀ := by
  intro x hx
  rcases hx with ⟨hxF, hxCentA⟩
  refine Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  apply Subtype.ext
  have haG : (a : G) ∈ section8SubgroupInAmbient A₀ :=
    Subgroup.mem_map_of_mem (section8FittingSubgroup M).subtype ha
  have haA : (a : G) ∈ section8CentralizerInFitting M A₀ :=
    section8SubgroupInAmbient_le_centralizerInFitting hA₀ haG
  exact Subgroup.mem_centralizer_iff.mp hxCentA (a : G) haA

/-- Prime-order elements outside `π(C_{F(M)}(A₀))` cannot centralize `C_{F(M)}(A₀)`.
This is the elementwise form of the argument proving (8.3). -/
public theorem CFSG.section8_prime_order_mem_centralizerInFitting_centralizer_eq_one
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {q : Nat.Primes} (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    {r : Nat.Primes}
    (hrA : r ∉ subgroupPrimeSet (section8CentralizerInFitting M A₀))
    {x : G}
    (hxAcent : x ∈ Subgroup.centralizer (section8CentralizerInFitting M A₀ : Set G))
    (hxord : orderOf x = r.val) :
    x = 1 := by
  let F : Subgroup G := section8FittingSubgroup M
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let R : Subgroup G := Subgroup.zpowers x
  have hπA_eq_F : subgroupPrimeSet A = subgroupPrimeSet F := by
    simpa [A, F] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hrF : r ∉ subgroupPrimeSet F := by
    intro hr
    exact hrA (by
      change r ∈ subgroupPrimeSet A
      rw [hπA_eq_F]
      exact hr)
  have hxM : x ∈ M := by
    simpa [A] using section8_centralizer_centralizerInFitting_le_maximal hM hqF A₀ hxAcent
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) := by
    have hFNorm : (F.subgroupOf M).Normal := by
      simpa [F] using section8FittingSubgroup_normal_in M
    let : (F.subgroupOf M).Normal := hFNorm
    exact Subgroup.le_normalizer_of_normal_subgroupOf (by simpa [F] using section8FittingSubgroup_le M)
  have hxNormF : x ∈ Subgroup.normalizer (F : Set G) := hMnormF hxM
  have hRnormF : R ≤ Subgroup.normalizer (F : Set G) := by
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    exact (Subgroup.normalizer (F : Set G)).zpow_mem hxNormF n
  have : Subgroup.Normalizes R F := ⟨hRnormF⟩
  have hR_le_centA : R ≤ Subgroup.centralizer (A : Set G) := by
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    exact (Subgroup.centralizer (A : Set G)).zpow_mem (by simpa [A] using hxAcent) n
  let C : Subgroup G := subgroupCentralizerIn F R
  have hA_le_C : A ≤ C := by
    intro a ha
    refine ⟨by exact section8CentralizerInFitting_le M A₀ ha, ?_⟩
    change a ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyCentA : y ∈ Subgroup.centralizer (A : Set G) := hR_le_centA hy
    exact (Subgroup.mem_centralizer_iff.mp hyCentA a ha).symm
  have hfixed_eq :
      fixedPointSubgroup R F = C.subgroupOf F := by
    simpa [C, F, R] using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn F R hRnormF
  have hcentralizer_fixed_le :
      Subgroup.centralizer (fixedPointSubgroup R F : Set F) ≤ fixedPointSubgroup R F := by
    rw [hfixed_eq]
    intro y hy
    have hyCentA : (y : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haC : a ∈ C := hA_le_C ha
      let aF : F := ⟨a, haC.1⟩
      have haCsub : aF ∈ C.subgroupOf F := by
        change a ∈ C
        exact haC
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy aF haCsub)
    have hyA : (y : G) ∈ A :=
      section8_subgroupCentralizerIn_fitting_centralizerInFitting_le hA₀
        ⟨y.property, hyCentA⟩
    have hyC : (y : G) ∈ C := hA_le_C hyA
    change (y : G) ∈ C
    exact hyC
  have hcardR : Nat.card R = r.val := by
    simpa [R, Nat.card_zpowers] using hxord
  have hcop : Nat.Coprime (Nat.card R) (Nat.card F) := by
    have hcop' : Nat.Coprime r.val (Nat.card F) :=
      r.2.coprime_iff_not_dvd.mpr hrF
    simpa [hcardR] using hcop'
  have htriv : ActsTrivially (A := R) (G := F) :=
    proposition_1_10 (G := F) (A := R) (section8FittingSubgroup_isNilpotent M) hcop
      hcentralizer_fixed_le
  have hxCentF : x ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    let r0 : R := ⟨x, by simp [R]⟩
    let fF : F := ⟨f, hf⟩
    have hfix : r0 • fF = fF := htriv r0 fF
    have hconj : x * f * x⁻¹ = f := by
      simpa [r0, fF, R, F, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        using congrArg Subtype.val hfix
    have hmul := congrArg (fun t : G => t * x) hconj
    simpa [mul_assoc] using hmul.symm
  let xM : M := ⟨x, hxM⟩
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hxCentFitM : xM ∈ Subgroup.centralizer (fittingSubgroup M : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfF : (f : G) ∈ F := by
      have hfSub : f ∈ F.subgroupOf M := by
        simpa [F, section8FittingSubgroup_subgroupOf_eq M] using hf
      exact hfSub
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxCentF (f : G) hfF)
  have hxFitM : xM ∈ fittingSubgroup M :=
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hMsolv hxCentFitM
  have hxF : x ∈ F := by
    have hxSub : xM ∈ F.subgroupOf M := by
      simpa [F, section8FittingSubgroup_subgroupOf_eq M] using hxFitM
    exact hxSub
  have hrFmem : r ∈ subgroupPrimeSet F := by
    have horderF : orderOf (⟨x, hxF⟩ : F) = r.val := by
      simpa [Subgroup.orderOf_coe] using hxord
    have hdvd : r.val ∣ Nat.card F := by
      simpa [horderF] using orderOf_dvd_natCard (⟨x, hxF⟩ : F)
    exact hdvd
  exact False.elim (hrF hrFmem)

/-- Equation (8.3): `C_G(C_{F(M)}(A₀))` is a `π(C_{F(M)}(A₀))`-subgroup. -/
public theorem CFSG.section8_centralizer_centralizerInFitting_isPiSubgroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {q : Nat.Primes} (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M)) :
    IsPiSubgroup (G := G) (subgroupPrimeSet (section8CentralizerInFitting M A₀))
      (Subgroup.centralizer (section8CentralizerInFitting M A₀ : Set G)) := by
  intro r hrC
  by_contra hrA
  let C : Subgroup G := Subgroup.centralizer (section8CentralizerInFitting M A₀ : Set G)
  let : Fact r.val.Prime := ⟨r.2⟩
  rcases exists_prime_orderOf_dvd_card' (G := C) r.val (by simpa [C] using hrC) with
    ⟨x, hxord⟩
  have hxordG : orderOf (x : G) = r.val := by
    simpa [Subgroup.orderOf_coe] using hxord
  have hx_eq_one :
      (x : G) = 1 :=
    section8_prime_order_mem_centralizerInFitting_centralizer_eq_one
      hM hqF hA₀ hrA x.property hxordG
  have hr_one : r.val = 1 := by
    rw [← hxord]
    exact orderOf_eq_one_iff.mpr (Subtype.ext hx_eq_one)
  exact r.2.ne_one hr_one

/-- The `O_{π(A)'}` part of (8.3), isolated from the proof that `C_G(A)` is a
`π(A)`-subgroup. -/
public theorem CFSG.section8CentralizerInFitting_piCore_centralizer_eq_bot_of_isPiSubgroup
    [Finite G] (M : Subgroup G) (A₀ : Subgroup (section8FittingSubgroup M))
    (hCπ :
      IsPiSubgroup (G := G) (subgroupPrimeSet (section8CentralizerInFitting M A₀))
        (Subgroup.centralizer (section8CentralizerInFitting M A₀ : Set G))) :
    piCoreIn (subgroupPrimeSet (section8CentralizerInFitting M A₀))ᶜ
      (Subgroup.centralizer (section8CentralizerInFitting M A₀ : Set G)) = ⊥ :=
  section8_piCoreIn_compl_eq_bot_of_isPiSubgroup hCπ

/-- The `O_{π(A)'}` conclusion of (8.3) for `A = C_{F(M)}(A₀)`. -/
public theorem CFSG.section8CentralizerInFitting_piCore_centralizer_eq_bot
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {q : Nat.Primes} (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M)) :
    piCoreIn (subgroupPrimeSet (section8CentralizerInFitting M A₀))ᶜ
      (Subgroup.centralizer (section8CentralizerInFitting M A₀ : Set G)) = ⊥ :=
  section8CentralizerInFitting_piCore_centralizer_eq_bot_of_isPiSubgroup M A₀
    (section8_centralizer_centralizerInFitting_isPiSubgroup hM hqF hA₀)

/-- In the Hypothesis 7.1 verification for `A = C_{F(M)}(A₀)`, the fixed points in an
`A`-invariant `π(A)'`-subgroup under a nontrivial singleton core of `Z(F(M))` are
trivial. -/
public theorem CFSG.section8_subgroupCentralizerIn_HFamily_piCore_center_eq_bot
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    {X Y : Subgroup G}
    (_hAX : section8CentralizerInFitting M A₀ ≤ X)
    (hY : Y ∈ section7HFamily X (section8CentralizerInFitting M A₀)
      (subgroupPrimeSet (section8CentralizerInFitting M A₀))ᶜ)
    {r : Nat.Primes} (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M)) :
    subgroupCentralizerIn Y
        (piCoreIn ({r} : Set Nat.Primes) (section8CenterInFitting M)) = ⊥ := by
  classical
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let F : Subgroup G := section8FittingSubgroup M
  let R : Subgroup G := piCoreIn ({r} : Set Nat.Primes) (section8CenterInFitting M)
  have hR_le_A : R ≤ A := by
    simpa [R, A] using
      section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ r
  have hnormR_eq : Subgroup.normalizer (R : Set G) = M := by
    simpa [R] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hrF
  have hCfix_le_M : subgroupCentralizerIn Y R ≤ M := by
    intro c hc
    have hc_norm : c ∈ Subgroup.normalizer (R : Set G) := by
      refine Subgroup.mem_normalizer_fintype ?_
      intro z hzR
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 z hzR
      have hconj : c * z * c⁻¹ = z := by
        calc
          c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [← hcomm]
          _ = z := by simp [mul_assoc]
      simpa [hconj] using hzR
    simpa [hnormR_eq] using hc_norm
  have hπeq : subgroupPrimeSet A = subgroupPrimeSet F := by
    simpa [A, F] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hFπ : IsPiSubgroup (G := G) (subgroupPrimeSet A) F := by
    intro q hqF
    rw [hπeq]
    exact hqF
  have hYF_bot : Y ⊓ F = ⊥ :=
    section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
      (π := subgroupPrimeSet A) (H := Y ⊓ F) (Y := Y) (C := F)
      inf_le_left inf_le_right (by simpa [A] using hY.2.1) hFπ
  have hcomm_AM_le_F : ⁅A, M⁆ ≤ F := by
    simpa [A, F, Subgroup.commutator_comm] using
      section8_commutator_maximal_le_fitting_of_le_fitting
        M (section8CentralizerInFitting_le M A₀)
  have hCfix_le_centA : subgroupCentralizerIn Y R ≤ Subgroup.centralizer (A : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a haA
    have hcM : c ∈ M := hCfix_le_M hc
    have hcommF : ⁅a, c⁆ ∈ F :=
      hcomm_AM_le_F (Subgroup.commutator_mem_commutator haA hcM)
    have hconjY : a * c * a⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hY.2.2 haA) c).1 hc.1
    have hcommY : ⁅a, c⁆ ∈ Y := by
      rw [commutatorElement_def]
      exact Y.mul_mem hconjY (Y.inv_mem hc.1)
    have hcommInf : ⁅a, c⁆ ∈ Y ⊓ F := ⟨hcommY, hcommF⟩
    have hcommBot : ⁅a, c⁆ ∈ (⊥ : Subgroup G) := by
      simpa [hYF_bot] using hcommInf
    have hcommOne : ⁅a, c⁆ = 1 := by
      simpa using hcommBot
    exact commutatorElement_eq_one_iff_mul_comm.mp hcommOne
  exact
    section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
      (π := subgroupPrimeSet A) (H := subgroupCentralizerIn Y R) (Y := Y)
      (C := Subgroup.centralizer (A : Set G))
      inf_le_left hCfix_le_centA (by simpa [A] using hY.2.1)
      (by
        simpa [A] using section8_centralizer_centralizerInFitting_isPiSubgroup hM hpF hA₀)

/-- Equation (8.5) for a family member, with the auxiliary prime already chosen. -/
public theorem CFSG.section8_HFamily_centralizerInFitting_le_singleton_compl_core_of_ne
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    {X Y : Subgroup G}
    (hAX : section8CentralizerInFitting M A₀ ≤ X) (hXproper : X ≠ ⊤)
    (hY : Y ∈ section7HFamily X (section8CentralizerInFitting M A₀)
      (subgroupPrimeSet (section8CentralizerInFitting M A₀))ᶜ)
    {q r : Nat.Primes}
    (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hrq : r ≠ q) :
    Y ≤ piCoreIn ({q} : Set Nat.Primes)ᶜ X := by
  classical
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let R : Subgroup G := piCoreIn ({r} : Set Nat.Primes) (section8CenterInFitting M)
  have hY_ne_top : Y ≠ ⊤ := by
    intro hYtop
    have htop_le_X : (⊤ : Subgroup G) ≤ X := by
      simpa [hYtop] using hY.1
    exact hXproper (top_le_iff.mp htop_le_X)
  have hsolvY : Group.IsSolvable Y :=
    IsMinCE.proper_subgroups_solvable Y (lt_top_iff_ne_top.mpr hY_ne_top)
  have hπeq :
      subgroupPrimeSet A = subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [A] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hrA : r ∈ subgroupPrimeSet A := by
    simpa [hπeq] using hrF
  have hR_le_A : R ≤ A := by
    simpa [R, A] using
      section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ r
  have hR_norm_Y : R ≤ Subgroup.normalizer (Y : Set G) :=
    hR_le_A.trans (by simpa [A] using hY.2.2)
  have hR_p : IsPGroup r.val R := by
    simpa [R] using section8_piCoreIn_singleton_centerInFitting_isPGroup M r
  have hcop : Nat.Coprime (Nat.card R) (Nat.card Y) :=
    section8_coprime_card_of_isPGroup_of_isPiSubgroup_compl
      (π := subgroupPrimeSet A) hrA hR_p (by simpa [A] using hY.2.1)
  have hfix : subgroupCentralizerIn Y R = ⊥ := by
    simpa [R] using
      section8_subgroupCentralizerIn_HFamily_piCore_center_eq_bot
        hM hpF hA₀ hAX hY hrF
  have hY_le_comm : Y ≤ ⁅Y, R⁆ :=
    section8_le_commutator_of_subgroupCentralizerIn_eq_bot
      hsolvY hR_norm_Y hcop hfix
  have hR_le_qcore :
      R ≤ piCoreIn ({q} : Set Nat.Primes)ᶜ X := by
    simpa [R] using
      section8_piCoreIn_singleton_centerInFitting_le_singleton_compl_core
        hM A₀ hAX hXproper hqF hrF hrq
  exact hY_le_comm.trans
    (section8_commutator_le_piCoreIn_of_right_le hY.1 hR_le_qcore)

/-- Equation (8.5): every `A`-invariant `π(A)'`-subgroup of a proper overgroup of
`A = C_{F(M)}(A₀)` lies in each singleton complement core `O_{q'}(X)` for
`q ∈ π(A)`. -/
public theorem CFSG.section8_HFamily_centralizerInFitting_le_singleton_compl_core
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    {X Y : Subgroup G}
    (hAX : section8CentralizerInFitting M A₀ ≤ X) (hXproper : X ≠ ⊤)
    (hY : Y ∈ section7HFamily X (section8CentralizerInFitting M A₀)
      (subgroupPrimeSet (section8CentralizerInFitting M A₀))ᶜ)
    {q : Nat.Primes}
    (hqA : q ∈ subgroupPrimeSet (section8CentralizerInFitting M A₀)) :
    Y ≤ piCoreIn ({q} : Set Nat.Primes)ᶜ X := by
  classical
  let A : Subgroup G := section8CentralizerInFitting M A₀
  have hπeq :
      subgroupPrimeSet A = subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [A] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [A, hπeq] using hqA
  by_cases hqp : q = ⟨p, Fact.out⟩
  · rcases section8CentralizerInFitting_exists_prime_ne_of_not_isPGroup
      hnFp A₀ with ⟨r, hrA, hrnep⟩
    have hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M) := by
      simpa [A, hπeq] using hrA
    have hrq : r ≠ q := by
      intro hrq_eq
      exact hrnep (hrq_eq.trans hqp)
    exact
      section8_HFamily_centralizerInFitting_le_singleton_compl_core_of_ne
        hM hpF hA₀ hAX hXproper hY hqF hrF hrq
  · have hpne : (⟨p, Fact.out⟩ : Nat.Primes) ≠ q := by
      intro hpq
      exact hqp hpq.symm
    exact
      section8_HFamily_centralizerInFitting_le_singleton_compl_core_of_ne
        hM hpF hA₀ hAX hXproper hY hqF hpF hpne

/-- A public Section 8 wrapper: a transported `π`-core belongs to the Section 7 family
whenever the parameter subgroup normalizes the ambient subgroup. -/
public theorem CFSG.section8_piCoreIn_mem_section7HFamily_of_le_normalizer
    [Finite G] {π : Set Nat.Primes} {H P : Subgroup G}
    (hPH : P ≤ Subgroup.normalizer (H : Set G)) :
    piCoreIn π H ∈ section7HFamily H P π := by
  refine ⟨piCoreIn_le (G := G) π H, piCoreIn_isPiSubgroup (G := G) π H, ?_⟩
  exact section8_le_normalizer_piCoreIn_of_le_normalizer hPH

/-- Membership in a Section 7 family gives containment in the subgroup it generates. -/
public theorem CFSG.section8_le_section7Generated_of_mem
    {H A Q : Subgroup G} {π : Set Nat.Primes}
    (hQ : Q ∈ section7HFamily H A π) :
    Q ≤ section7Generated H A π := by
  change Q ≤ sSup (section7HFamily H A π)
  exact le_sSup hQ

/-- The easy containment in Hypothesis 7.1: if `A ≤ X`, then the transported
`π`-core of `X` is contained in the generated Section 7 family. -/
public theorem CFSG.section8_piCoreIn_le_section7Generated_of_le
    [Finite G] {A X : Subgroup G} {π : Set Nat.Primes}
    (hAX : A ≤ X) :
    piCoreIn π X ≤ section7Generated X A π :=
  section8_le_section7Generated_of_mem
    (section8_piCoreIn_mem_section7HFamily_of_le_normalizer
      (π := π) (H := X) (P := A) (hAX.trans Subgroup.le_normalizer))

/-- `C_{F(M)}(A₀)` satisfies Hypothesis 7.1 in the non-`p` branch of Section 8. -/
public theorem CFSG.section8CentralizerInFitting_Hypothesis7_1
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M)) :
    Hypothesis7_1 (section8CentralizerInFitting M A₀) :=
  section8CentralizerInFitting_Hypothesis7_1_of_generated_eq hM hA₀ hA₀rank
    (by
      intro X hAX hXproper
      apply le_antisymm
      · refine sSup_le ?_
        intro Y hY
        exact
          section8_le_piCoreIn_compl_of_forall_le_singleton_compl hY.1
            (by
              intro q hqA
              exact
                section8_HFamily_centralizerInFitting_le_singleton_compl_core
                  hM hpF hA₀ hnFp hAX hXproper hY hqA)
      · exact section8_piCoreIn_le_section7Generated_of_le hAX)

/-- For `A = C_{F(M)}(A₀)`, equations (8.3) and Theorem 7.2 make each relevant
top-level star family subsingleton, once Hypothesis 7.1 has been established. -/
public theorem CFSG.section8_HStarFamily_centralizerInFitting_subsingleton
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {r : Nat.Primes} (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {q : Nat.Primes}
    (hq : q ∉ subgroupPrimeSet (section8CentralizerInFitting M A₀)) :
    Subsingleton {Q : Subgroup G //
      Q ∈ section7HStarFamily (⊤ : Subgroup G)
        (section8CentralizerInFitting M A₀) ({q} : Set Nat.Primes)} := by
  let A : Subgroup G := section8CentralizerInFitting M A₀
  have hcenterRank : 3 ≤ groupRank (Subgroup.center A) := by
    simpa [A] using section8CentralizerInFitting_center_rank_ge hA₀ hA₀rank
  have htrans : ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) := by
    simpa [A] using theorem_7_2 (G := G) hHyp hq hcenterRank
  have hKbot : section7K A = ⊥ := by
    simpa [A, section7K] using
      section8CentralizerInFitting_piCore_centralizer_eq_bot hM hrF hA₀
  refine ⟨?_⟩
  intro Q₁ Q₂
  apply Subtype.ext
  rcases htrans Q₁ Q₁.property Q₂ Q₂.property with ⟨k, hk⟩
  have hk1 : (k : G) = 1 := by
    have hkbot : (k : G) ∈ (⊥ : Subgroup G) := by
      simpa [hKbot] using k.property
    simpa using hkbot
  have hconj1 : (Q₁ : Subgroup G).conjBy (1 : G) = Q₁ :=
    section8_conjBy_one (Q₁ : Subgroup G)
  rw [hk1, hconj1] at hk
  exact hk.symm

/-- For `A = C_{F(M)}(A₀)`, Theorem 7.4 embeds the `H^*` family for `F(M)` into
the corresponding `H^*` family for `A`, once Hypothesis 7.1 has been established. -/
public theorem CFSG.section8_HStarFamily_fitting_subset_centralizerInFitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {q : Nat.Primes}
    (hq : q ∉ subgroupPrimeSet (section8CentralizerInFitting M A₀)) :
    section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
        ({q} : Set Nat.Primes) ⊆
      section7HStarFamily (⊤ : Subgroup G)
        (section8CentralizerInFitting M A₀) ({q} : Set Nat.Primes) := by
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let F : Subgroup G := section8FittingSubgroup M
  have hcenterRank : 3 ≤ groupRank (Subgroup.center A) := by
    simpa [A] using section8CentralizerInFitting_center_rank_ge hA₀ hA₀rank
  have htrans : ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) := by
    simpa [A] using theorem_7_2 (G := G) hHyp hq hcenterRank
  have hF_ne_top : F ≠ ⊤ := by
    simpa [F] using section8_ne_top_of_le_maximal hM (section8FittingSubgroup_le M)
  have hAsubnormal : IsSubnormalIn A F := by
    simpa [A, F] using section8CentralizerInFitting_isSubnormalIn_fitting M A₀
  have hFπ : IsPiSubgroup (G := G) (subgroupPrimeSet A) F := by
    intro r hrF
    have hπeq : subgroupPrimeSet A = subgroupPrimeSet F := by
      simpa [A, F] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
    simpa [hπeq]
  have hres :=
    theorem_7_4 (G := G) (A := A) (P := F)
      (by simpa [A] using hHyp) (by simpa [A] using hq)
      hF_ne_top hAsubnormal hFπ htrans
  exact hres.2.2.1

/-- Under the Section 8 part-(a) hypotheses, the `H_G^*(F(M);q)` family is
subsingleton for primes outside `π(C_{F(M)}(A₀))`. -/
public theorem CFSG.section8_HStarFamily_fitting_subsingleton_of_centralizerInFitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {r : Nat.Primes} (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {q : Nat.Primes}
    (hq : q ∉ subgroupPrimeSet (section8CentralizerInFitting M A₀)) :
    Subsingleton {Q : Subgroup G //
      Q ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
        ({q} : Set Nat.Primes)} := by
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let F : Subgroup G := section8FittingSubgroup M
  have hsubset :
      section7HStarFamily (⊤ : Subgroup G) F ({q} : Set Nat.Primes) ⊆
        section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    simpa [A, F] using
      section8_HStarFamily_fitting_subset_centralizerInFitting
        hM hA₀ hA₀rank hHyp hq
  have hsubA :
      Subsingleton {Q : Subgroup G //
        Q ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)} := by
    simpa [A] using
      section8_HStarFamily_centralizerInFitting_subsingleton
        hM hrF hA₀ hA₀rank hHyp hq
  refine ⟨?_⟩
  intro Q₁ Q₂
  apply Subtype.ext
  have h₁ : (Q₁ : Subgroup G) ∈
      section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    hsubset Q₁.property
  have h₂ : (Q₂ : Subgroup G) ∈
      section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    hsubset Q₂.property
  have hEq :=
    Subsingleton.elim
      (⟨(Q₁ : Subgroup G), h₁⟩ :
        {Q : Subgroup G //
          Q ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)})
      (⟨(Q₂ : Subgroup G), h₂⟩ :
        {Q : Subgroup G //
          Q ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)})
  exact congrArg
    (fun R : {Q : Subgroup G //
        Q ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)} =>
      (R : Subgroup G)) hEq

/-- In the part-(a) setup, maximality makes every `H_G^*(F(M);q)` member normalized
by `M`. -/
public theorem CFSG.section8_HStarFamily_fitting_le_normalizer_maximal_of_centralizerInFitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {r : Nat.Primes} (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {q : Nat.Primes}
    (hq : q ∉ subgroupPrimeSet (section8CentralizerInFitting M A₀))
    {Q : Subgroup G}
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
      ({q} : Set Nat.Primes)) :
    M ≤ Subgroup.normalizer (Q : Set G) := by
  have hMnormF : M ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
    have hFNorm : ((section8FittingSubgroup M).subgroupOf M).Normal :=
      section8FittingSubgroup_normal_in M
    let : ((section8FittingSubgroup M).subgroupOf M).Normal := hFNorm
    exact Subgroup.le_normalizer_of_normal_subgroupOf (section8FittingSubgroup_le M)
  have hsubF :
      Subsingleton {R : Subgroup G //
        R ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
          ({q} : Set Nat.Primes)} :=
    section8_HStarFamily_fitting_subsingleton_of_centralizerInFitting
      hM hrF hA₀ hA₀rank hHyp hq
  intro m hm
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hx
  have hQconj : Q.conjBy m ∈
      section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
        ({q} : Set Nat.Primes) :=
    section8_mem_section7HStarFamily_top_conjBy_of_mem_normalizer (hMnormF hm) hQ
  have hQconj_eq : Q.conjBy m = Q := by
    have hEq :=
      Subsingleton.elim
        (⟨Q.conjBy m, hQconj⟩ :
          {R : Subgroup G //
            R ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
              ({q} : Set Nat.Primes)})
        (⟨Q, hQ⟩ :
          {R : Subgroup G //
            R ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
              ({q} : Set Nat.Primes)})
    exact congrArg Subtype.val hEq
  have hx_conj : m * x * m⁻¹ ∈ Q.conjBy m :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  simpa [hQconj_eq] using hx_conj

/-- In the part-(a) setup, every `H_G^*(F(M);q)` member is trivial for
`q ∉ π(F(M))`. -/
public theorem CFSG.section8_HStarFamily_fitting_eq_bot_of_centralizerInFitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {r : Nat.Primes} (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {q : Nat.Primes}
    (hqF : q ∉ subgroupPrimeSet (section8FittingSubgroup M))
    {Q : Subgroup G}
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
      ({q} : Set Nat.Primes)) :
    Q = ⊥ := by
  by_contra hQ_ne_bot
  have hAπF :
      subgroupPrimeSet (section8CentralizerInFitting M A₀) =
        subgroupPrimeSet (section8FittingSubgroup M) :=
    section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hqA : q ∉ subgroupPrimeSet (section8CentralizerInFitting M A₀) := by
    intro hq
    exact hqF (by simpa [hAπF] using hq)
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
    hQ.1.2.1
  let : Fact q.val.Prime := ⟨q.2⟩
  have hQp : IsPGroup q.val Q :=
    _root_.CFSG.isPGroup_of_isPiSubgroup_singleton hQπ
  have hQ_ne_top : Q ≠ ⊤ := by
    intro hQ_top
    subst hQ_top
    let : Nontrivial ↥(⊤ : Subgroup G) :=
      (Subgroup.nontrivial_iff_ne_bot (H := (⊤ : Subgroup G))).2 (by simpa using hQ_ne_bot)
    let : Nontrivial G := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).injective.nontrivial
    have htop_q : IsPGroup q.val (⊤ : Subgroup G) :=
      _root_.CFSG.isPGroup_of_isPiSubgroup_singleton hQπ
    have hGq : IsPGroup q.val G := htop_q.of_equiv Subgroup.topEquiv
    have hcenter_nontrivial : Nontrivial (Subgroup.center G) :=
      IsPGroup.center_nontrivial (p := q.val) (G := G) hGq
    have hcenter_ne_bot : Subgroup.center G ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (H := Subgroup.center G)).1 hcenter_nontrivial
    exact hcenter_ne_bot (center_eq_bot_of_min_ce (G := G))
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    section8_HStarFamily_fitting_le_normalizer_maximal_of_centralizerInFitting
      hM hrF hA₀ hA₀rank hHyp hqA hQ
  have hnorm_ne_top : Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
    intro hnorm_top
    have hQnorm : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
    let : IsSimpleGroup G := IsMinCE.simple
    rcases (haveI := hQnorm; IsSimpleGroup.eq_bot_or_eq_top_of_normal Q) with hQbot | hQtop
    · exact hQ_ne_bot hQbot
    · exact hQ_ne_top hQtop
  have hnorm_eq : Subgroup.normalizer (Q : Set G) = M :=
    section8MaximalSubgroups_eq_of_le hM hMnormQ hnorm_ne_top
  have hQM : Q ≤ M := by
    simpa [hnorm_eq] using (Subgroup.le_normalizer : Q ≤ Subgroup.normalizer (Q : Set G))
  have hQnormM : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
  have hQnilM : Group.IsNilpotent (Q.subgroupOf M) := by
    have hQnil : Group.IsNilpotent Q :=
      IsPGroup.isNilpotent (p := q.val) (G := Q) hQp
    let e : Q.subgroupOf M ≃* Q := Subgroup.subgroupOfEquivOfLe hQM
    exact Group.nilpotent_of_mulEquiv (G := Q) (G' := Q.subgroupOf M) e.symm
  have hQsub_le_fit : Q.subgroupOf M ≤ fittingSubgroup M :=
    le_sSup ⟨hQnormM, hQnilM⟩
  have hQ_le_F : Q ≤ section8FittingSubgroup M := by
    intro x hxQ
    have hxM : x ∈ M := hQM hxQ
    let xM : M := ⟨x, hxM⟩
    have hxQsub : xM ∈ Q.subgroupOf M := by
      change x ∈ Q
      exact hxQ
    have hxFit : xM ∈ fittingSubgroup M := hQsub_le_fit hxQsub
    have hxFsub : xM ∈ (section8FittingSubgroup M).subgroupOf M := by
      simpa [section8FittingSubgroup_subgroupOf_eq M] using hxFit
    exact hxFsub
  let QF : Subgroup (section8FittingSubgroup M) :=
    Q.subgroupOf (section8FittingSubgroup M)
  have hQF_p : IsPGroup q.val QF := by
    exact hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQ_le_F).symm
  have hQF_ne_bot : QF ≠ ⊥ := by
    intro hQF_bot
    have hQ_eq : Q = QF.map (section8FittingSubgroup M).subtype := by
      simpa [QF] using (Subgroup.map_subgroupOf_eq_of_le hQ_le_F).symm
    exact hQ_ne_bot (by simpa [QF, hQF_bot] using hQ_eq)
  have hqFmem : q ∈ subgroupPrimeSet (section8FittingSubgroup M) :=
    section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
      (A := section8FittingSubgroup M) (B := QF) hQF_p hQF_ne_bot
  exact hqF hqFmem

/-- In the part-(a) setup, every member of `H_G^*(C_{F(M)}(A₀);q)` is trivial
for `q ∉ π(C_{F(M)}(A₀))`, once Hypothesis 7.1 has been established. -/
public theorem CFSG.section8_HStarFamily_centralizerInFitting_eq_bot
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {r : Nat.Primes} (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {q : Nat.Primes}
    (hq : q ∉ subgroupPrimeSet (section8CentralizerInFitting M A₀))
    {Q : Subgroup G}
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G)
      (section8CentralizerInFitting M A₀) ({q} : Set Nat.Primes)) :
    Q = ⊥ := by
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let F : Subgroup G := section8FittingSubgroup M
  have hπeq : subgroupPrimeSet A = subgroupPrimeSet F := by
    simpa [A, F] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hqF : q ∉ subgroupPrimeSet F := by
    intro hqF
    exact hq (by rw [hπeq]; exact hqF)
  have hbotF : (⊥ : Subgroup G) ∈
      section7HFamily (⊤ : Subgroup G) F ({q} : Set Nat.Primes) :=
    by
      refine ⟨bot_le, ?_, ?_⟩
      · intro s hs
        exfalso
        have hs_one : s.val ∣ (1 : ℕ) := by
          simpa using hs
        exact s.2.not_dvd_one hs_one
      · intro a _ha
        refine Subgroup.mem_normalizer_fintype ?_
        intro x hx
        have hx_one : x = 1 := by simpa using hx
        simp [hx_one]
  rcases section8_exists_mem_section7HStarFamily_of_mem_family hbotF with
    ⟨QF, hQFstar, _hbot_le_QF⟩
  have hsubset :
      section7HStarFamily (⊤ : Subgroup G) F ({q} : Set Nat.Primes) ⊆
        section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    simpa [A, F] using
      section8_HStarFamily_fitting_subset_centralizerInFitting
        hM hA₀ hA₀rank hHyp hq
  have hsubA :
      Subsingleton {R : Subgroup G //
        R ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)} := by
    simpa [A] using
      section8_HStarFamily_centralizerInFitting_subsingleton
        hM hrF hA₀ hA₀rank hHyp hq
  have hQ_eq_QF : Q = QF := by
    have hEq :=
      Subsingleton.elim
        (⟨Q, by simpa [A] using hQ⟩ :
          {R : Subgroup G //
            R ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)})
        (⟨QF, hsubset hQFstar⟩ :
          {R : Subgroup G //
            R ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)})
    exact congrArg Subtype.val hEq
  have hQF_bot : QF = ⊥ :=
    section8_HStarFamily_fitting_eq_bot_of_centralizerInFitting
      hM hrF hA₀ hA₀rank hHyp hqF hQFstar
  exact hQ_eq_QF.trans hQF_bot

/-- In the part-(a) setup, the singleton-prime Section 7 family for
`A = C_{F(M)}(A₀)` is exactly `{⊥}`, once Hypothesis 7.1 has been established. -/
public theorem CFSG.section8_HFamily_centralizerInFitting_eq_singleton_bot
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {r : Nat.Primes} (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {q : Nat.Primes}
    (hq : q ∉ subgroupPrimeSet (section8CentralizerInFitting M A₀)) :
    section7HFamily (⊤ : Subgroup G)
      (section8CentralizerInFitting M A₀) ({q} : Set Nat.Primes) =
        ({⊥} : Set (Subgroup G)) := by
  ext R
  constructor
  · intro hR
    rcases section8_exists_mem_section7HStarFamily_of_mem_family hR with
      ⟨Q, hQstar, hRQ⟩
    have hQbot : Q = ⊥ :=
      section8_HStarFamily_centralizerInFitting_eq_bot
        hM hrF hA₀ hA₀rank hHyp hq hQstar
    have hRbot : R = ⊥ :=
      le_bot_iff.mp (by simpa [hQbot] using hRQ)
    simp [hRbot]
  · intro hR
    have hRbot : R = ⊥ := by simpa using hR
    rw [hRbot]
    refine ⟨bot_le, ?_, ?_⟩
    · intro s hs
      exfalso
      have hs_one : s.val ∣ (1 : ℕ) := by
        simpa using hs
      exact s.2.not_dvd_one hs_one
    · intro a _ha
      refine Subgroup.mem_normalizer_fintype ?_
      intro x hx
      have hx_one : x = 1 := by simpa using hx
      simp [hx_one]

/-- A nontrivial singleton-prime subgroup of a minimal counterexample is proper. -/
public theorem CFSG.section8_ne_top_of_isPiSubgroup_singleton_ne_bot
    [Finite G] [IsMinCE G] {Q : Subgroup G} {q : Nat.Primes}
    (hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q)
    (hQ_ne_bot : Q ≠ ⊥) :
    Q ≠ ⊤ := by
  intro hQ_top
  subst hQ_top
  let : Fact q.val.Prime := ⟨q.2⟩
  let : Nontrivial ↥(⊤ : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot (H := (⊤ : Subgroup G))).2 (by simpa using hQ_ne_bot)
  let : Nontrivial G := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).injective.nontrivial
  have htop_q : IsPGroup q.val (⊤ : Subgroup G) :=
    section8_isPGroup_of_isPiSubgroup_singleton hQπ
  have hGq : IsPGroup q.val G := htop_q.of_equiv Subgroup.topEquiv
  have hcenter_nontrivial : Nontrivial (Subgroup.center G) :=
    IsPGroup.center_nontrivial (p := q.val) (G := G) hGq
  have hcenter_ne_bot : Subgroup.center G ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (H := Subgroup.center G)).1 hcenter_nontrivial
  exact hcenter_ne_bot (center_eq_bot_of_min_ce (G := G))

/-- The trivial subgroup belongs to every top-level Section 7 `H` family. -/
public theorem CFSG.section8_bot_mem_section7HFamily_top
    [Finite G] (A : Subgroup G) (π : Set Nat.Primes) :
    (⊥ : Subgroup G) ∈ section7HFamily (⊤ : Subgroup G) A π := by
  refine ⟨bot_le, ?_, ?_⟩
  · intro q hq
    exfalso
    have hq_one : q.val ∣ (1 : ℕ) := by
      simpa using hq
    exact q.2.not_dvd_one hq_one
  · intro a _ha
    refine Subgroup.mem_normalizer_fintype ?_
    intro x hx
    have hx_one : x = 1 := by simpa using hx
    simp [hx_one]

/-- If `A` normalizes a family member `Y`, then it normalizes every transported singleton
`π`-core of `Y`. -/
public theorem CFSG.section8_piCoreIn_singleton_mem_section7HFamily_top_of_mem_family
    [Finite G] {A Y : Subgroup G} {π : Set Nat.Primes} {q : Nat.Primes}
    (hY : Y ∈ section7HFamily (⊤ : Subgroup G) A π) :
    piCoreIn ({q} : Set Nat.Primes) Y ∈
      section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
  refine ⟨le_top, piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes) Y, ?_⟩
  exact section8_le_normalizer_piCoreIn_of_le_normalizer hY.2.2


/-- The first prime-support consequence of (8.6): in the part-(a) setup, the Fitting
subgroup of any maximal overgroup of `C_{F(M)}(A₀)` has no primes outside
`π(C_{F(M)}(A₀))`, once Hypothesis 7.1 has been established. -/
public theorem CFSG.section8FittingSubgroup_primeSet_subset_centralizerInFitting_of_maximalOver
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    {r : Nat.Primes} (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    subgroupPrimeSet (section8FittingSubgroup N) ⊆
      subgroupPrimeSet (section8CentralizerInFitting M A₀) := by
  let A : Subgroup G := section8CentralizerInFitting M A₀
  intro q hqFN
  by_contra hqA
  let ZN : Subgroup G := section8CenterInFitting N
  let L : Subgroup G := piCoreIn ({q} : Set Nat.Primes) ZN
  have hqZN : q ∈ subgroupPrimeSet ZN := by
    have hπZN : subgroupPrimeSet ZN = subgroupPrimeSet (section8FittingSubgroup N) := by
      simpa [ZN] using section8CenterInFitting_primeSet_eq_fitting N
    simpa [hπZN] using hqFN
  have : IsMulCommutative ZN := by
    simpa [ZN] using section8CenterInFitting_isMulCommutative N
  have hL_ne_bot : L ≠ ⊥ := by
    simpa [L] using
      section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isMulCommutative
        (H := ZN) hqZN
  have hAN : A ≤ N := by
    simpa [A] using hN.2
  have hNnormZN : N ≤ Subgroup.normalizer (ZN : Set G) := by
    have hZNNorm : (ZN.subgroupOf N).Normal := by
      simpa [ZN] using section8CenterInFitting_normal_in_maximal N
    let : (ZN.subgroupOf N).Normal := hZNNorm
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (by simpa [ZN] using section8CenterInFitting_le_maximal N)
  have hA_norm_ZN : A ≤ Subgroup.normalizer (ZN : Set G) :=
    hAN.trans hNnormZN
  have hL_mem_ZN : L ∈ section7HFamily ZN A ({q} : Set Nat.Primes) := by
    simpa [L] using
      section8_piCoreIn_mem_section7HFamily_of_le_normalizer
        (π := ({q} : Set Nat.Primes)) (H := ZN) (P := A) hA_norm_ZN
  have hL_mem_top : L ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    ⟨le_top, hL_mem_ZN.2.1, hL_mem_ZN.2.2⟩
  have hfamily_eq :
      section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) =
        ({⊥} : Set (Subgroup G)) := by
    simpa [A] using
      section8_HFamily_centralizerInFitting_eq_singleton_bot
        hM hrF hA₀ hA₀rank hHyp hqA
  have hL_bot : L = ⊥ := by
    have hmem_single : L ∈ ({⊥} : Set (Subgroup G)) := by
      simpa [hfamily_eq] using hL_mem_top
    simpa using hmem_single
  exact hL_ne_bot hL_bot

/-- For a maximal proper subgroup `N`, the core outside the prime support of `F(N)` is
trivial. This is the formal version of
`F(O_{σ'}(N)) <= O_{σ'}(F(N)) = 1`, where `σ = π(F(N))`. -/
public theorem CFSG.section8_piCoreIn_fitting_primeSet_compl_maximal_eq_bot
    [Finite G] [IsMinCE G] {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroups G) :
    piCoreIn (subgroupPrimeSet (section8FittingSubgroup N))ᶜ N = ⊥ := by
  classical
  let σ : Set Nat.Primes := subgroupPrimeSet (section8FittingSubgroup N)
  let Y : Subgroup G := piCoreIn σᶜ N
  have hY_le_N : Y ≤ N := by
    simpa [Y, σ] using piCoreIn_le (G := G) σᶜ N
  have hYsub_norm : (Y.subgroupOf N).Normal := by
    have hsub_eq : Y.subgroupOf N = piCore σᶜ N := by
      simpa [Y, σ] using piCore_map_subtype_subgroupOf (G := G) σᶜ N
    rw [hsub_eq]
    infer_instance
  by_contra hY_ne_bot
  have hYsub_ne_bot : Y.subgroupOf N ≠ ⊥ := by
    intro hYsub_bot
    have hY_eq : Y = (Y.subgroupOf N).map N.subtype := by
      simpa [Y] using (Subgroup.map_subgroupOf_eq_of_le hY_le_N).symm
    exact hY_ne_bot (by simpa [hYsub_bot] using hY_eq)
  have hNsolv : Group.IsSolvable N :=
    IsMinCE.proper_subgroups_solvable N (lt_top_iff_ne_top.mpr hN.1)
  let : Group.IsSolvable N := hNsolv
  have hYsub_solv : Group.IsSolvable (Y.subgroupOf N) := by infer_instance
  let : Group.IsSolvable (Y.subgroupOf N) := hYsub_solv
  have hfitY_ne_bot : fittingSubgroup (Y.subgroupOf N) ≠ ⊥ := by
    intro hfitY
    have hcardY : Nat.card (Y.subgroupOf N) = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable (Y.subgroupOf N)).mp hfitY
    exact hYsub_ne_bot ((Subgroup.card_eq_one (H := Y.subgroupOf N)).1 hcardY)
  let L_N : Subgroup N := fittingSubgroupOf (G := N) (Y.subgroupOf N)
  have hL_N_ne_bot : L_N ≠ ⊥ := by
    intro hLbot
    apply hfitY_ne_bot
    change (fittingSubgroup (Y.subgroupOf N)).map (Y.subgroupOf N).subtype = ⊥ at hLbot
    have hLbot' :
        (fittingSubgroup (Y.subgroupOf N)).map (Y.subgroupOf N).subtype =
          (⊥ : Subgroup (Y.subgroupOf N)).map (Y.subgroupOf N).subtype := by
      simpa using hLbot
    exact Subgroup.map_injective (Y.subgroupOf N).subtype_injective hLbot'
  let L : Subgroup G := L_N.map N.subtype
  have hL_ne_bot : L ≠ ⊥ := by
    intro hLbot
    apply hL_N_ne_bot
    exact Subgroup.map_injective N.subtype_injective (by simpa [L] using hLbot)
  have hL_N_le_fitN : L_N ≤ fittingSubgroup N :=
    fittingSubgroupOf_le_fittingSubgroup (G := N) (Y.subgroupOf N) hYsub_norm
  have hL_le_F : L ≤ section8FittingSubgroup N := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xN, hxL, rfl⟩
    change (xN : G) ∈ section8FittingSubgroup N
    refine Subgroup.mem_map.mpr ?_
    exact ⟨⟨(xN : G), xN.property⟩, hL_N_le_fitN hxL, rfl⟩
  have hL_N_le_Ysub : L_N ≤ Y.subgroupOf N :=
    fittingSubgroupOf_le (G := N) (Y.subgroupOf N)
  have hL_le_Y : L ≤ Y := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xN, hxL, rfl⟩
    exact hL_N_le_Ysub hxL
  have hYπ : IsPiSubgroup (G := G) σᶜ Y := by
    simpa [Y, σ] using piCoreIn_isPiSubgroup (G := G) σᶜ N
  have hFπ : IsPiSubgroup (G := G) σ (section8FittingSubgroup N) := by
    intro q hq
    change q ∈ subgroupPrimeSet (section8FittingSubgroup N)
    exact hq
  have hL_bot : L = ⊥ :=
    section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
      (π := σ) (H := L) (Y := Y) (C := section8FittingSubgroup N)
      hL_le_Y hL_le_F hYπ hFπ
  exact hL_ne_bot hL_bot

/-- The second prime-support consequence for a maximal overgroup `N` of
`A = C_{F(M)}(A₀)`: the Fitting subgroup of `N` has exactly the same prime support
as `A`, hence as `F(M)`. -/
public theorem CFSG.section8FittingSubgroup_primeSet_eq_centralizerInFitting_of_maximalOver
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    subgroupPrimeSet (section8FittingSubgroup N) =
      subgroupPrimeSet (section8CentralizerInFitting M A₀) := by
  classical
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let σ : Set Nat.Primes := subgroupPrimeSet (section8FittingSubgroup N)
  apply Set.Subset.antisymm
  · simpa [A, σ] using
      section8FittingSubgroup_primeSet_subset_centralizerInFitting_of_maximalOver
        hM hpF hA₀ hA₀rank hHyp hN
  · intro q hqA
    have hσ_subset_A : σ ⊆ subgroupPrimeSet A := by
      simpa [A, σ] using
        section8FittingSubgroup_primeSet_subset_centralizerInFitting_of_maximalOver
          hM hpF hA₀ hA₀rank hHyp hN
    have hAπF : subgroupPrimeSet A = subgroupPrimeSet (section8FittingSubgroup M) := by
      simpa [A] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
    have hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M) := by
      simpa [A, hAπF] using hqA
    by_contra hqσ
    let Rq : Subgroup G := piCoreIn ({q} : Set Nat.Primes) (section8CenterInFitting M)
    have hqZ : q ∈ subgroupPrimeSet (section8CenterInFitting M) := by
      have hZπ : subgroupPrimeSet (section8CenterInFitting M) =
          subgroupPrimeSet (section8FittingSubgroup M) :=
        section8CenterInFitting_primeSet_eq_fitting M
      simpa [hZπ] using hqF
    have : IsMulCommutative (section8CenterInFitting M) :=
      section8CenterInFitting_isMulCommutative M
    have hRq_ne_bot : Rq ≠ ⊥ := by
      simpa [Rq] using
        section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isMulCommutative
          (H := section8CenterInFitting M) hqZ
    have hRq_le_N : Rq ≤ N := by
      simpa [Rq, A] using
        (section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ q).trans
          hN.2
    have hRq_le_core : Rq ≤ piCoreIn σᶜ N := by
      refine section8_le_piCoreIn_compl_of_forall_le_singleton_compl hRq_le_N ?_
      intro s hsσ
      have hsA : s ∈ subgroupPrimeSet A := hσ_subset_A hsσ
      have hsF : s ∈ subgroupPrimeSet (section8FittingSubgroup M) := by
        simpa [hAπF] using hsA
      have hsq : s ≠ q := by
        intro hsq
        exact hqσ (by simpa [σ, hsq] using hsσ)
      simpa [Rq, σ] using
        section8_piCoreIn_singleton_centerInFitting_le_singleton_compl_core
          hM A₀ hN.2 hN.1.1 hsF hqF hsq.symm
    have hcore_bot : piCoreIn σᶜ N = ⊥ := by
      simpa [σ] using section8_piCoreIn_fitting_primeSet_compl_maximal_eq_bot hN.1
    have hRq_bot : Rq = ⊥ :=
      le_bot_iff.mp (by simpa [hcore_bot] using hRq_le_core)
    exact hRq_ne_bot hRq_bot

/-- Each singleton component of `F(N)` for a maximal overgroup `N` of
`A = C_{F(M)}(A₀)` centralizes every distinct singleton component of `Z(F(M))`.
This is the commutator calculation behind equation (8.7). -/
public theorem CFSG.section8_piCoreIn_singleton_fitting_maximalOver_le_centralizer_centerInFitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀))
    {q r : Nat.Primes}
    (hqFN : q ∈ subgroupPrimeSet (section8FittingSubgroup N))
    (hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M)) (hrq : r ≠ q) :
    piCoreIn ({q} : Set Nat.Primes) (section8FittingSubgroup N) ≤
      Subgroup.centralizer
        (piCoreIn ({r} : Set Nat.Primes) (section8CenterInFitting M) : Set G) := by
  classical
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let FN : Subgroup G := section8FittingSubgroup N
  let Dq : Subgroup G := piCoreIn ({q} : Set Nat.Primes) FN
  let Cq : Subgroup G := piCoreIn ({q} : Set Nat.Primes)ᶜ N
  let Rr : Subgroup G := piCoreIn ({r} : Set Nat.Primes) (section8CenterInFitting M)
  have hσeq :
      subgroupPrimeSet FN = subgroupPrimeSet A := by
    simpa [FN, A] using
      section8FittingSubgroup_primeSet_eq_centralizerInFitting_of_maximalOver
        hM hpF hA₀ hA₀rank hHyp hN
  have hqA : q ∈ subgroupPrimeSet A := by
    simpa [FN, hσeq] using hqFN
  have hAπF : subgroupPrimeSet A = subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [A] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [hAπF] using hqA
  have hRr_le_Cq : Rr ≤ Cq := by
    simpa [Rr, Cq] using
      section8_piCoreIn_singleton_centerInFitting_le_singleton_compl_core
        hM A₀ hN.2 hN.1.1 hqF hrF hrq
  have hDq_le_N : Dq ≤ N := by
    have hDq_le_FN : Dq ≤ FN := by
      simpa [Dq, FN] using
        piCoreIn_le (G := G) ({q} : Set Nat.Primes) (section8FittingSubgroup N)
    exact hDq_le_FN.trans (by simpa [FN] using section8FittingSubgroup_le N)
  have hCq_le_N : Cq ≤ N := by
    simpa [Cq] using piCoreIn_le (G := G) ({q} : Set Nat.Primes)ᶜ N
  have hN_norm_FN : N ≤ Subgroup.normalizer (FN : Set G) := by
    have hFN_norm : (FN.subgroupOf N).Normal := by
      simpa [FN] using section8FittingSubgroup_normal_in N
    let : (FN.subgroupOf N).Normal := hFN_norm
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (by simpa [FN] using section8FittingSubgroup_le N)
  have hN_norm_Dq : N ≤ Subgroup.normalizer (Dq : Set G) := by
    simpa [Dq, FN] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({q} : Set Nat.Primes)) (H := FN) (P := N) hN_norm_FN
  have hDq_norm_N : (Dq.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDq_le_N).mpr hN_norm_Dq
  have hCq_norm_N : (Cq.subgroupOf N).Normal := by
    have hsub_eq : Cq.subgroupOf N = piCore ({q} : Set Nat.Primes)ᶜ N := by
      simpa [Cq] using piCore_map_subtype_subgroupOf (G := G) ({q} : Set Nat.Primes)ᶜ N
    rw [hsub_eq]
    infer_instance
  have hDqπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Dq := by
    simpa [Dq, FN] using
      piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes) (section8FittingSubgroup N)
  have hCqπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ Cq := by
    simpa [Cq] using piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ N
  have hDqNπ : IsPiSubgroup (G := N) ({q} : Set Nat.Primes) (Dq.subgroupOf N) := by
    intro s hs
    have hcard : Nat.card (Dq.subgroupOf N) = Nat.card Dq :=
      natCard_subgroupOf_eq _ _ hDq_le_N
    exact hDqπ s (by simpa [hcard] using hs)
  have hCqNπ : IsPiSubgroup (G := N) ({q} : Set Nat.Primes)ᶜ (Cq.subgroupOf N) := by
    intro s hs
    have hcard : Nat.card (Cq.subgroupOf N) = Nat.card Cq :=
      natCard_subgroupOf_eq _ _ hCq_le_N
    exact hCqπ s (by simpa [hcard] using hs)
  have hDqCq_inf_bot : Dq.subgroupOf N ⊓ Cq.subgroupOf N = ⊥ := by
    exact
      section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
        (G := N) (π := ({q} : Set Nat.Primes))
        (H := Dq.subgroupOf N ⊓ Cq.subgroupOf N)
        (Y := Cq.subgroupOf N) (C := Dq.subgroupOf N)
        inf_le_right inf_le_left hCqNπ hDqNπ
  intro d hdDq
  rw [Subgroup.mem_centralizer_iff]
  intro x hxRr
  let dN : N := ⟨d, hDq_le_N hdDq⟩
  let xN : N := ⟨x, hCq_le_N (hRr_le_Cq hxRr)⟩
  have hdN : dN ∈ Dq.subgroupOf N := by
    change d ∈ Dq
    exact hdDq
  have hxN : xN ∈ Cq.subgroupOf N := by
    change x ∈ Cq
    exact hRr_le_Cq hxRr
  let : (Dq.subgroupOf N).Normal := hDq_norm_N
  let : (Cq.subgroupOf N).Normal := hCq_norm_N
  have hcomm_mem :
      ⁅dN, xN⁆ ∈ ⁅Dq.subgroupOf N, Cq.subgroupOf N⁆ :=
    Subgroup.commutator_mem_commutator hdN hxN
  have hcomm_inf : ⁅dN, xN⁆ ∈ Dq.subgroupOf N ⊓ Cq.subgroupOf N :=
    Subgroup.commutator_le_inf (H₁ := Dq.subgroupOf N) (H₂ := Cq.subgroupOf N)
      hcomm_mem
  have hcomm_bot : ⁅dN, xN⁆ ∈ (⊥ : Subgroup N) := by
    simpa [hDqCq_inf_bot] using hcomm_inf
  have hcomm_one_N : ⁅dN, xN⁆ = 1 := by
    simpa using hcomm_bot
  have hcomm_one_G : ⁅d, x⁆ = (1 : G) := by
    have hval := congrArg Subtype.val hcomm_one_N
    change ((↑(⁅dN, xN⁆) : G) = 1) at hval
    simpa [dN, xN, commutatorElement_def] using hval
  have hmul_dx : d * x = x * d :=
    commutatorElement_eq_one_iff_mul_comm.mp hcomm_one_G
  exact hmul_dx.symm

/-- Each singleton component of `F(N)` for a maximal overgroup `N` of
`A = C_{F(M)}(A₀)` is contained in the original maximal subgroup `M`. -/
public theorem CFSG.section8_piCoreIn_singleton_fitting_maximalOver_le_original
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀))
    {q : Nat.Primes} (hqFN : q ∈ subgroupPrimeSet (section8FittingSubgroup N)) :
    piCoreIn ({q} : Set Nat.Primes) (section8FittingSubgroup N) ≤ M := by
  classical
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let FN : Subgroup G := section8FittingSubgroup N
  let Dq : Subgroup G := piCoreIn ({q} : Set Nat.Primes) FN
  let Cq : Subgroup G := piCoreIn ({q} : Set Nat.Primes)ᶜ N
  have hσeq :
      subgroupPrimeSet FN = subgroupPrimeSet A := by
    simpa [FN, A] using
      section8FittingSubgroup_primeSet_eq_centralizerInFitting_of_maximalOver
        hM hpF hA₀ hA₀rank hHyp hN
  have hqA : q ∈ subgroupPrimeSet A := by
    simpa [FN, hσeq] using hqFN
  have hAπF : subgroupPrimeSet A = subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [A] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [hAπF] using hqA
  obtain ⟨r, hrF, hrq⟩ :
      ∃ r : Nat.Primes, r ∈ subgroupPrimeSet (section8FittingSubgroup M) ∧ r ≠ q := by
    by_cases hqp : q = ⟨p, Fact.out⟩
    · rcases section8CentralizerInFitting_exists_prime_ne_of_not_isPGroup
        hnFp A₀ with ⟨r, hrA, hrnep⟩
      refine ⟨r, ?_, ?_⟩
      · simpa [A, hAπF] using hrA
      · intro hrq'
        exact hrnep (hrq'.trans hqp)
    · refine ⟨⟨p, Fact.out⟩, hpF, ?_⟩
      intro hpq
      exact hqp hpq.symm
  let Rr : Subgroup G := piCoreIn ({r} : Set Nat.Primes) (section8CenterInFitting M)
  have hRr_le_Cq : Rr ≤ Cq := by
    simpa [Rr, Cq] using
      section8_piCoreIn_singleton_centerInFitting_le_singleton_compl_core
        hM A₀ hN.2 hN.1.1 hqF hrF hrq
  have hDq_le_N : Dq ≤ N := by
    have hDq_le_FN : Dq ≤ FN := by
      simpa [Dq, FN] using
        piCoreIn_le (G := G) ({q} : Set Nat.Primes) (section8FittingSubgroup N)
    exact hDq_le_FN.trans (by simpa [FN] using section8FittingSubgroup_le N)
  have hCq_le_N : Cq ≤ N := by
    simpa [Cq] using piCoreIn_le (G := G) ({q} : Set Nat.Primes)ᶜ N
  have hN_norm_FN : N ≤ Subgroup.normalizer (FN : Set G) := by
    have hFN_norm : (FN.subgroupOf N).Normal := by
      simpa [FN] using section8FittingSubgroup_normal_in N
    let : (FN.subgroupOf N).Normal := hFN_norm
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (by simpa [FN] using section8FittingSubgroup_le N)
  have hN_norm_Dq : N ≤ Subgroup.normalizer (Dq : Set G) := by
    simpa [Dq, FN] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({q} : Set Nat.Primes)) (H := FN) (P := N) hN_norm_FN
  have hDq_norm_N : (Dq.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDq_le_N).mpr hN_norm_Dq
  have hCq_norm_N : (Cq.subgroupOf N).Normal := by
    have hsub_eq : Cq.subgroupOf N = piCore ({q} : Set Nat.Primes)ᶜ N := by
      simpa [Cq] using piCore_map_subtype_subgroupOf (G := G) ({q} : Set Nat.Primes)ᶜ N
    rw [hsub_eq]
    infer_instance
  have hDqπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Dq := by
    simpa [Dq, FN] using
      piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes) (section8FittingSubgroup N)
  have hCqπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ Cq := by
    simpa [Cq] using piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ N
  have hDqNπ : IsPiSubgroup (G := N) ({q} : Set Nat.Primes) (Dq.subgroupOf N) := by
    intro s hs
    have hcard : Nat.card (Dq.subgroupOf N) = Nat.card Dq :=
      natCard_subgroupOf_eq _ _ hDq_le_N
    exact hDqπ s (by simpa [hcard] using hs)
  have hCqNπ : IsPiSubgroup (G := N) ({q} : Set Nat.Primes)ᶜ (Cq.subgroupOf N) := by
    intro s hs
    have hcard : Nat.card (Cq.subgroupOf N) = Nat.card Cq :=
      natCard_subgroupOf_eq _ _ hCq_le_N
    exact hCqπ s (by simpa [hcard] using hs)
  have hDqCq_inf_bot : Dq.subgroupOf N ⊓ Cq.subgroupOf N = ⊥ := by
    exact
      section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
        (G := N) (π := ({q} : Set Nat.Primes))
        (H := Dq.subgroupOf N ⊓ Cq.subgroupOf N)
        (Y := Cq.subgroupOf N) (C := Dq.subgroupOf N)
        inf_le_right inf_le_left hCqNπ hDqNπ
  have hDq_le_cent_Rr : Dq ≤ Subgroup.centralizer (Rr : Set G) := by
    intro d hdDq
    rw [Subgroup.mem_centralizer_iff]
    intro x hxRr
    let dN : N := ⟨d, hDq_le_N hdDq⟩
    let xN : N := ⟨x, hCq_le_N (hRr_le_Cq hxRr)⟩
    have hdN : dN ∈ Dq.subgroupOf N := by
      change d ∈ Dq
      exact hdDq
    have hxN : xN ∈ Cq.subgroupOf N := by
      change x ∈ Cq
      exact hRr_le_Cq hxRr
    let : (Dq.subgroupOf N).Normal := hDq_norm_N
    let : (Cq.subgroupOf N).Normal := hCq_norm_N
    have hcomm_mem :
        ⁅dN, xN⁆ ∈ ⁅Dq.subgroupOf N, Cq.subgroupOf N⁆ :=
      Subgroup.commutator_mem_commutator hdN hxN
    have hcomm_inf : ⁅dN, xN⁆ ∈ Dq.subgroupOf N ⊓ Cq.subgroupOf N :=
      Subgroup.commutator_le_inf (H₁ := Dq.subgroupOf N) (H₂ := Cq.subgroupOf N)
        hcomm_mem
    have hcomm_bot : ⁅dN, xN⁆ ∈ (⊥ : Subgroup N) := by
      simpa [hDqCq_inf_bot] using hcomm_inf
    have hcomm_one_N : ⁅dN, xN⁆ = 1 := by
      simpa using hcomm_bot
    have hcomm_one_G : ⁅d, x⁆ = (1 : G) := by
      have hval := congrArg Subtype.val hcomm_one_N
      change ((↑(⁅dN, xN⁆) : G) = 1) at hval
      simpa [dN, xN, commutatorElement_def] using hval
    have hmul_dx : d * x = x * d :=
      commutatorElement_eq_one_iff_mul_comm.mp hcomm_one_G
    exact hmul_dx.symm
  have hDq_le_norm_Rr : Dq ≤ Subgroup.normalizer (Rr : Set G) :=
    hDq_le_cent_Rr.trans (centralizer_le_normalizer Rr)
  have hnorm_Rr : Subgroup.normalizer (Rr : Set G) = M := by
    simpa [Rr] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hrF
  simpa [Dq, Rr, hnorm_Rr] using hDq_le_norm_Rr

/-- The Fitting subgroup of any maximal overgroup `N` of `A = C_{F(M)}(A₀)` is
contained in the original maximal subgroup `M`. This is the formal version of
the conclusion `D <= M` after equation (8.7). -/
public theorem CFSG.section8FittingSubgroup_maximalOver_le_original
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    section8FittingSubgroup N ≤ M := by
  classical
  let FN : Subgroup G := section8FittingSubgroup N
  let K : Subgroup FN := M.comap FN.subtype
  have hnilFN : Group.IsNilpotent FN := by
    simpa [FN] using section8FittingSubgroup_isNilpotent N
  let : Group.IsNilpotent FN := hnilFN
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup FN) := by
    let e : FN ≃* (⊤ : Subgroup FN) :=
      (Subgroup.topEquiv : (⊤ : Subgroup FN) ≃* FN).symm
    exact Group.nilpotent_of_mulEquiv (G := FN) (G' := (⊤ : Subgroup FN)) e
  have htop_le_sup :
      (⊤ : Subgroup FN) ≤
        ⨆ q : (Nat.card FN).primeFactors.attach, pCore q.1.1 FN :=
    normal_nilpotent_le_sup_pCore
      (G := FN) (N := (⊤ : Subgroup FN)) (hN := inferInstance) htop_nil
  have hsup_le_K :
      (⨆ q : (Nat.card FN).primeFactors.attach, pCore q.1.1 FN) ≤ K := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    have : Fact q.val.Prime := ⟨q.2⟩
    have hqFN : q ∈ subgroupPrimeSet FN := by
      exact Nat.dvd_of_mem_primeFactors q0.1.2
    intro x hx
    change (x : G) ∈ M
    have hxD : (x : G) ∈ piCoreIn ({q} : Set Nat.Primes) FN := by
      have hxmap : (x : G) ∈ (pCore q.val FN).map FN.subtype :=
        Subgroup.mem_map_of_mem FN.subtype (by simpa [q] using hx)
      simpa [section8_piCoreIn_singleton_eq_pCore_map q FN] using hxmap
    exact
      section8_piCoreIn_singleton_fitting_maximalOver_le_original
        hM hpF hA₀ hA₀rank hnFp hHyp hN hqFN hxD
  intro x hxFN
  let xFN : FN := ⟨x, hxFN⟩
  have hxK : xFN ∈ K := by
    have hxTop : xFN ∈ (⊤ : Subgroup FN) := Subgroup.mem_top xFN
    exact hsup_le_K (htop_le_sup hxTop)
  exact hxK

/-- Monotonicity for transported singleton `π`-cores when the larger subgroup normalizes
the smaller one. -/
public theorem CFSG.section8_piCoreIn_singleton_le_of_le_normalizer
    [Finite G] {Y H : Subgroup G} (hYH : Y ≤ H)
    (hHnormY : H ≤ Subgroup.normalizer (Y : Set G)) (q : Nat.Primes) :
    piCoreIn ({q} : Set Nat.Primes) Y ≤ piCoreIn ({q} : Set Nat.Primes) H := by
  classical
  let P : Subgroup G := piCoreIn ({q} : Set Nat.Primes) Y
  have hP_le_Y : P ≤ Y := by
    simpa [P] using piCoreIn_le (G := G) ({q} : Set Nat.Primes) Y
  have hP_le_H : P ≤ H := hP_le_Y.trans hYH
  have hH_norm_P : H ≤ Subgroup.normalizer (P : Set G) := by
    simpa [P] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({q} : Set Nat.Primes)) (H := Y) (P := H) hHnormY
  have hPsub_norm : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_H).mpr hH_norm_P
  have hPπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) P := by
    simpa [P] using piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes) Y
  have hPsubπ : IsPiSubgroup (G := H) ({q} : Set Nat.Primes) (P.subgroupOf H) := by
    intro s hs
    have hcard : Nat.card (P.subgroupOf H) = Nat.card P :=
      natCard_subgroupOf_eq _ _ hP_le_H
    exact hPπ s (by simpa [hcard] using hs)
  have hPsub_le_core : P.subgroupOf H ≤ piCore ({q} : Set Nat.Primes) H :=
    le_sSup
      (show P.subgroupOf H ∈
          {K : Subgroup H | K.Normal ∧ IsPiSubgroup (G := H) ({q} : Set Nat.Primes) K} from
        ⟨hPsub_norm, hPsubπ⟩)
  intro x hxP
  let xH : H := ⟨x, hP_le_H hxP⟩
  have hxPsub : xH ∈ P.subgroupOf H := by
    change x ∈ P
    exact hxP
  have hxCore : xH ∈ piCore ({q} : Set Nat.Primes) H :=
    hPsub_le_core hxPsub
  exact Subgroup.mem_map.mpr ⟨xH, hxCore, rfl⟩

/-- A normal `π`-subgroup of an ambient subgroup lies in the transported `π`-core. -/
public theorem CFSG.section8_le_piCoreIn_of_normal_isPiSubgroup
    [Finite G] {π : Set Nat.Primes} {K H : Subgroup G} (hKH : K ≤ H)
    (hKnormH : (K.subgroupOf H).Normal) (hKπ : IsPiSubgroup (G := G) π K) :
    K ≤ piCoreIn π H := by
  have hKsubπ : IsPiSubgroup (G := H) π (K.subgroupOf H) := by
    intro q hq
    have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
      natCard_subgroupOf_eq K H hKH
    exact hKπ q (by simpa [hcard] using hq)
  have hKsub_le_core : K.subgroupOf H ≤ piCore π H :=
    le_sSup
      (show K.subgroupOf H ∈ {L : Subgroup H | L.Normal ∧ IsPiSubgroup (G := H) π L} from
        ⟨hKnormH, hKsubπ⟩)
  intro x hxK
  let xH : H := ⟨x, hKH hxK⟩
  have hxKsub : xH ∈ K.subgroupOf H := by
    change x ∈ K
    exact hxK
  exact Subgroup.mem_map.mpr ⟨xH, hKsub_le_core hxKsub, rfl⟩

/-- The `p'`-core of `F(N)` centralizes the `p`-component of `Z(F(M))` for every
maximal overgroup `N` of `A = C_{F(M)}(A₀)`. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_fitting_maximalOver_le_centralizer_centerInFitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ (section8FittingSubgroup N) ≤
      Subgroup.centralizer
        (piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes) (section8CenterInFitting M) :
          Set G) := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let FN : Subgroup G := section8FittingSubgroup N
  let Y : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ FN
  let Rp : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes) (section8CenterInFitting M)
  let C : Subgroup Y := (Subgroup.centralizer (Rp : Set G)).comap Y.subtype
  have hY_le_FN : Y ≤ FN := by
    simpa [Y, FN] using
      piCoreIn_le (G := G) ({p₀} : Set Nat.Primes)ᶜ (section8FittingSubgroup N)
  have hnilFN : Group.IsNilpotent FN := by
    simpa [FN] using section8FittingSubgroup_isNilpotent N
  let : Group.IsNilpotent FN := hnilFN
  have hnilY : Group.IsNilpotent Y := by
    have hYsub_nil : Group.IsNilpotent (Y.subgroupOf FN) := by infer_instance
    let e : Y.subgroupOf FN ≃* Y := Subgroup.subgroupOfEquivOfLe hY_le_FN
    exact Group.nilpotent_of_mulEquiv (G := Y.subgroupOf FN) (G' := Y) e
  let : Group.IsNilpotent Y := hnilY
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup Y) := by
    let e : Y ≃* (⊤ : Subgroup Y) :=
      (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).symm
    exact Group.nilpotent_of_mulEquiv (G := Y) (G' := (⊤ : Subgroup Y)) e
  have htop_le_sup :
      (⊤ : Subgroup Y) ≤
        ⨆ q : (Nat.card Y).primeFactors.attach, pCore q.1.1 Y :=
    normal_nilpotent_le_sup_pCore
      (G := Y) (N := (⊤ : Subgroup Y)) (hN := inferInstance) htop_nil
  have hFN_norm_Y : FN ≤ Subgroup.normalizer (Y : Set G) := by
    simpa [Y, FN] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({p₀} : Set Nat.Primes)ᶜ)
        (H := FN) (P := FN) (Subgroup.le_normalizer)
  have hYπ : IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ Y := by
    simpa [Y, FN] using
      piCoreIn_isPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ
        (section8FittingSubgroup N)
  have hsup_le_C :
      (⨆ q : (Nat.card Y).primeFactors.attach, pCore q.1.1 Y) ≤ C := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    have : Fact q.val.Prime := ⟨q.2⟩
    have hqY : q ∈ subgroupPrimeSet Y := by
      exact Nat.dvd_of_mem_primeFactors q0.1.2
    have hpq : p₀ ≠ q := by
      have hq_compl : q ∈ ({p₀} : Set Nat.Primes)ᶜ := hYπ q hqY
      intro hpq
      exact hq_compl (by simp [hpq])
    have hqFN : q ∈ subgroupPrimeSet FN :=
      section8_subgroupPrimeSet_mono hY_le_FN hqY
    have hDq_cent_Rp :
        piCoreIn ({q} : Set Nat.Primes) FN ≤ Subgroup.centralizer (Rp : Set G) := by
      simpa [FN, Rp, p₀] using
        section8_piCoreIn_singleton_fitting_maximalOver_le_centralizer_centerInFitting
          hM hpF hA₀ hA₀rank hHyp hN hqFN hpF hpq
    intro x hx
    change ((x : Y) : G) ∈ Subgroup.centralizer (Rp : Set G)
    have hxYcore : ((x : Y) : G) ∈ piCoreIn ({q} : Set Nat.Primes) Y := by
      have hxmap : ((x : Y) : G) ∈ (pCore q.val Y).map Y.subtype :=
        Subgroup.mem_map_of_mem Y.subtype (by simpa [q] using hx)
      simpa [section8_piCoreIn_singleton_eq_pCore_map q Y] using hxmap
    have hxFNcore : ((x : Y) : G) ∈ piCoreIn ({q} : Set Nat.Primes) FN :=
      section8_piCoreIn_singleton_le_of_le_normalizer hY_le_FN hFN_norm_Y q hxYcore
    exact hDq_cent_Rp hxFNcore
  intro y hyY
  let yY : Y := ⟨y, hyY⟩
  have hyC : yY ∈ C := by
    have hyTop : yY ∈ (⊤ : Subgroup Y) := Subgroup.mem_top yY
    exact hsup_le_C (htop_le_sup hyTop)
  exact hyC

/-- Coprime-action wrapper: if an element acts trivially on the Fitting subgroup of a
finite solvable group, then it acts trivially on the whole group. -/
public theorem CFSG.section8_element_actsTrivially_of_centralizes_fitting_of_coprime
    {K R : Type*} [Group K] [Finite K] [Group R] [MulDistribMulAction R K]
    (hsolv : Group.IsSolvable K) (hcoprime : Nat.Coprime (Nat.card R) (Nat.card K))
    (r : R) (hr_fitting : ∀ f : fittingSubgroup K, r • (f : K) = (f : K)) :
    ∀ k : K, r • k = k := by
  classical
  have hcop_r : Nat.Coprime (orderOf r) (Nat.card K) :=
    Nat.Coprime.of_dvd_left (orderOf_dvd_natCard r) hcoprime
  intro k
  set x : K := k⁻¹ * (r • k) with hx_def
  have hx_centralizer :
      x ∈ Subgroup.centralizer (fittingSubgroup K : Set K) := by
    refine (Subgroup.mem_centralizer_iff (g := x) (s := (fittingSubgroup K : Set K))).2 ?_
    intro f hf
    have hf_fix : r • f = f := hr_fitting ⟨f, hf⟩
    have hconj : k * f * k⁻¹ ∈ fittingSubgroup K :=
      Subgroup.Normal.conj_mem (inferInstance : (fittingSubgroup K).Normal) f hf k
    have hconj_fix : r • (k * f * k⁻¹) = k * f * k⁻¹ :=
      hr_fitting ⟨k * f * k⁻¹, hconj⟩
    have hconj_eq : k * f * k⁻¹ = (r • k) * f * (r • k)⁻¹ := by
      have : (r • k) * f * (r • k)⁻¹ = k * f * k⁻¹ := by
        simpa [smul_mul', smul_inv', hf_fix, mul_assoc] using hconj_fix
      simpa using this.symm
    have h1 : k * f * k⁻¹ * (r • k) = (r • k) * f := by
      calc
        k * f * k⁻¹ * (r • k) =
            ((r • k) * f * (r • k)⁻¹) * (r • k) := by
          simpa [mul_assoc] using congrArg (fun t : K => t * (r • k)) hconj_eq
        _ = (r • k) * f := by simp [mul_assoc]
    have h2 : f * k⁻¹ * (r • k) = k⁻¹ * (r • k) * f := by
      have := congrArg (fun t : K => k⁻¹ * t) h1
      simpa [mul_assoc] using this
    simpa [hx_def, mul_assoc] using h2
  have hx_mem_fit : x ∈ fittingSubgroup K :=
    (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := K) hsolv)
      hx_centralizer
  have hx_fix : r • x = x := by
    simpa using hr_fitting ⟨x, hx_mem_fit⟩
  have hx_fix_pow : ∀ n : ℕ, (r ^ n) • x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, mul_smul, hx_fix, ih]
  have hr_k : r • k = k * x := by simp [hx_def]
  have hpow : ∀ n : ℕ, (r ^ n) • k = k * x ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (r ^ (n + 1)) • k = (r ^ n) • (r • k) := by
            simp [pow_succ, mul_smul]
          _ = (r ^ n) • (k * x) := by simp [hr_k]
          _ = ((r ^ n) • k) * ((r ^ n) • x) := by simp [smul_mul']
          _ = (k * x ^ n) * x := by simp [ih, hx_fix_pow n]
          _ = k * x ^ (n + 1) := by simp [pow_succ, mul_assoc]
  have hx_pow_order : x ^ orderOf r = 1 := by
    have hr_pow : r ^ orderOf r = (1 : R) := pow_orderOf_eq_one r
    have : k = k * x ^ orderOf r := by
      calc
        k = (1 : R) • k := by simp
        _ = (r ^ orderOf r) • k := by simp [hr_pow]
        _ = k * x ^ orderOf r := hpow (orderOf r)
    have := congrArg (fun t : K => k⁻¹ * t) this
    simpa [mul_assoc] using this.symm
  have horder_dvd : orderOf x ∣ orderOf r :=
    (orderOf_dvd_iff_pow_eq_one).2 hx_pow_order
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_r horder_dvd (orderOf_dvd_natCard x)
  have hx_one : x = 1 := (orderOf_eq_one_iff).1 horder_one
  simp [hx_one, hr_k]

/-- Subgroup form of the preceding coprime-action wrapper. -/
public theorem CFSG.section8_le_centralizer_of_le_centralizer_fitting_of_coprime
    {K₀ : Type*} [Group K₀] [Finite K₀] {K R : Subgroup K₀}
    (hsolvK : Group.IsSolvable K) (hRnormK : R ≤ Subgroup.normalizer (K : Set K₀))
    (hcop : Nat.Coprime (Nat.card R) (Nat.card K))
    (hRcentFit : R ≤ Subgroup.centralizer (fittingSubgroupOf (G := K₀) K : Set K₀)) :
    R ≤ Subgroup.centralizer (K : Set K₀) := by
  classical
  have : Subgroup.Normalizes R K := ⟨hRnormK⟩
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let rR : R := ⟨r, hr⟩
  let kK : K := ⟨k, hk⟩
  have hr_fitting : ∀ f : fittingSubgroup K, rR • (f : K) = (f : K) := by
    intro f
    apply Subtype.ext
    have hfFit : ((f : K) : K₀) ∈ fittingSubgroupOf (G := K₀) K := by
      change ((f : K) : K₀) ∈ (fittingSubgroup K).map K.subtype
      exact Subgroup.mem_map_of_mem K.subtype f.property
    have hcomm := Subgroup.mem_centralizer_iff.mp (hRcentFit hr) ((f : K) : K₀) hfFit
    have hconj : r * ((f : K) : K₀) * r⁻¹ = ((f : K) : K₀) := by
      calc
        r * ((f : K) : K₀) * r⁻¹ = (((f : K) : K₀) * r) * r⁻¹ := by
          rw [← hcomm]
        _ = ((f : K) : K₀) := by simp [mul_assoc]
    simpa [rR, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hconj
  have hfix :
      rR • kK = kK :=
    section8_element_actsTrivially_of_centralizes_fitting_of_coprime
      (K := K) (R := R) hsolvK hcop rR hr_fitting kK
  have hconj : r * k * r⁻¹ = k := by
    simpa [rR, kK, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      using congrArg Subtype.val hfix
  have hmul := congrArg (fun t : K₀ => t * r) hconj
  simpa [mul_assoc] using hmul.symm

/-- For a maximal overgroup `N` of `A = C_{F(M)}(A₀)`, the `p'`-core of `N` is
contained in the original maximal subgroup `M`. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_maximalOver_le_original
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ N ≤ M := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let FN : Subgroup G := section8FittingSubgroup N
  let Rp : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes) (section8CenterInFitting M)
  let OpN_G : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ N
  let OpN : Subgroup N := pPrimeCore p N
  let R_N : Subgroup N := Rp.subgroupOf N
  have hRp_le_N : Rp ≤ N := by
    have hRp_le_A : Rp ≤ A := by
      simpa [Rp, A, p₀] using
        section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ p₀
    exact hRp_le_A.trans (by simpa [A] using hN.2)
  have hRp_p : IsPGroup p Rp := by
    simpa [Rp, p₀] using section8_piCoreIn_singleton_centerInFitting_isPGroup M p₀
  have hR_N_p : IsPGroup p R_N :=
    hRp_p.of_equiv (Subgroup.subgroupOfEquivOfLe hRp_le_N).symm
  have hNsolv : Group.IsSolvable N :=
    IsMinCE.proper_subgroups_solvable N (lt_top_iff_ne_top.mpr hN.1.1)
  let : Group.IsSolvable N := hNsolv
  have hOpNsolv : Group.IsSolvable OpN := by infer_instance
  have hcop_R_OpN : Nat.Coprime (Nat.card R_N) (Nat.card OpN) := by
    rcases hR_N_p.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (pPrimeCore_coprime_card (G := N) (p := p)).pow_left n
  have hR_norm_OpN : R_N ≤ Subgroup.normalizer (OpN : Set N) := by
    have hnorm_top : Subgroup.normalizer (OpN : Set N) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (inferInstance : OpN.Normal)
    rw [hnorm_top]
    exact le_top
  have hFitOpN_le_FN_G :
      (fittingSubgroupOf (G := N) OpN).map N.subtype ≤ FN := by
    have hFit_le_fitN : fittingSubgroupOf (G := N) OpN ≤ fittingSubgroup N :=
      fittingSubgroupOf_le_fittingSubgroup (G := N) OpN inferInstance
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xN, hxFit, rfl⟩
    change (xN : G) ∈ FN
    refine Subgroup.mem_map.mpr ?_
    exact ⟨xN, hFit_le_fitN hxFit, rfl⟩
  have hFitOpN_le_OpN_G :
      (fittingSubgroupOf (G := N) OpN).map N.subtype ≤ OpN_G := by
    have hFit_le_OpN : fittingSubgroupOf (G := N) OpN ≤ OpN :=
      fittingSubgroupOf_le (G := N) OpN
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xN, hxFit, rfl⟩
    have hxOpN : xN ∈ OpN := hFit_le_OpN hxFit
    have hxMap : (xN : G) ∈ (pPrimeCore p N).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hxOpN
    simpa [OpN_G, p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hxMap
  have hFitOpNπ :
      IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ
        ((fittingSubgroupOf (G := N) OpN).map N.subtype) := by
    have hOpNπ : IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ OpN_G := by
      simpa [OpN_G, p₀] using
        piCoreIn_isPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ N
    intro q hq
    exact hOpNπ q (hq.trans (Subgroup.card_dvd_of_le hFitOpN_le_OpN_G))
  have hFitOpN_norm_FN :
      (((fittingSubgroupOf (G := N) OpN).map N.subtype).subgroupOf FN).Normal := by
    let L_N : Subgroup N := fittingSubgroupOf (G := N) OpN
    let L_G : Subgroup G := L_N.map N.subtype
    have hL_norm_N : L_N.Normal := fittingSubgroupOf_normal (G := N) OpN inferInstance
    have hFN_le_N : FN ≤ N := section8FittingSubgroup_le N
    have hFN_norm_LG : FN ≤ Subgroup.normalizer (L_G : Set G) := by
      intro x hxFN
      refine Subgroup.mem_normalizer_fintype ?_
      intro y hyL
      rcases Subgroup.mem_map.mp hyL with ⟨yN, hyLN, rfl⟩
      let xN : N := ⟨x, hFN_le_N hxFN⟩
      have hconjN : xN * yN * xN⁻¹ ∈ L_N :=
        hL_norm_N.conj_mem yN hyLN xN
      exact Subgroup.mem_map.mpr ⟨xN * yN * xN⁻¹, hconjN, by simp [xN, mul_assoc]⟩
    have hLG_le_FN : L_G ≤ FN := by
      simpa [L_G, L_N] using hFitOpN_le_FN_G
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLG_le_FN).mpr hFN_norm_LG
  have hFitOpN_le_piCore_FN :
      (fittingSubgroupOf (G := N) OpN).map N.subtype ≤
        piCoreIn ({p₀} : Set Nat.Primes)ᶜ FN :=
    section8_le_piCoreIn_of_normal_isPiSubgroup
      hFitOpN_le_FN_G hFitOpN_norm_FN hFitOpNπ
  have hFitOpN_cent_Rp :
      (fittingSubgroupOf (G := N) OpN).map N.subtype ≤
        Subgroup.centralizer (Rp : Set G) := by
    exact hFitOpN_le_piCore_FN.trans (by
      simpa [FN, Rp, p₀] using
        section8_piCoreIn_singleton_compl_fitting_maximalOver_le_centralizer_centerInFitting
          hM hpF hA₀ hA₀rank hHyp hN)
  have hR_cent_FitOpN :
      R_N ≤ Subgroup.centralizer (fittingSubgroupOf (G := N) OpN : Set N) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfG : (f : G) ∈ (fittingSubgroupOf (G := N) OpN).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hf
    have hcentG : (f : G) ∈ Subgroup.centralizer (Rp : Set G) :=
      hFitOpN_cent_Rp hfG
    have hrRp : (r : G) ∈ Rp := by
      change (r : G) ∈ Rp at hr
      exact hr
    have hcommG := Subgroup.mem_centralizer_iff.mp hcentG (r : G) hrRp
    exact Subtype.ext hcommG.symm
  have hR_cent_OpN : R_N ≤ Subgroup.centralizer (OpN : Set N) :=
    section8_le_centralizer_of_le_centralizer_fitting_of_coprime
      hOpNsolv hR_norm_OpN hcop_R_OpN hR_cent_FitOpN
  have hOpN_G_le_cent_Rp : OpN_G ≤ Subgroup.centralizer (Rp : Set G) := by
    intro x hx
    have hxMap : x ∈ (pPrimeCore p N).map N.subtype := by
      simpa [OpN_G, p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hx
    rcases Subgroup.mem_map.mp hxMap with ⟨xN, hxOpN, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hrRp
    let rN : N := ⟨r, hRp_le_N hrRp⟩
    have hrRN : rN ∈ R_N := by
      change r ∈ Rp
      exact hrRp
    have hcommN := Subgroup.mem_centralizer_iff.mp (hR_cent_OpN hrRN) xN hxOpN
    exact (congrArg Subtype.val hcommN).symm
  have hnorm_Rp : Subgroup.normalizer (Rp : Set G) = M := by
    simpa [Rp, p₀] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hpF
  exact hOpN_G_le_cent_Rp.trans (by simpa [hnorm_Rp] using centralizer_le_normalizer Rp)

/-- The `p'`-core of `F(M)` centralizes `A₀`, hence lies in
`A = C_{F(M)}(A₀)`. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_fitting_le_centralizerInFitting
    [Finite G] {p : ℕ} [Fact p.Prime] (M : Subgroup G)
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M)) :
    piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ (section8FittingSubgroup M) ≤
      section8CentralizerInFitting M A₀ := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let F : Subgroup G := section8FittingSubgroup M
  let Y : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ F
  have hY_le_F : Y ≤ F := by
    simpa [Y, F] using piCoreIn_le (G := G) ({p₀} : Set Nat.Primes)ᶜ
      (section8FittingSubgroup M)
  have hY_eq : Y = (pPrimeCore p F).map F.subtype := by
    simp [Y, F, p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map]
  have hY_cent_pCore :
      Y ≤ Subgroup.centralizer (((pCore p F).map F.subtype) : Set G) := by
    have hcentF : pPrimeCore p F ≤ Subgroup.centralizer (pCore p F : Set F) :=
      pPrimeCore_le_centralizer_of_normal_pgroup
        (G := F) p (pCore p F) (pCore_isPGroup (G := F) (p := p))
    intro y hyY
    rw [hY_eq] at hyY
    rcases Subgroup.mem_map.mp hyY with ⟨yF, hyP, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨aF, haP, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hcentF hyP) aF haP)
  have hA₀p : IsPGroup p A₀ := by
    let : IsElementaryAbelian p A₀ := hA₀.1
    exact IsElementaryAbelian.isPGroup p A₀
  rcases IsPGroup.exists_le_sylow (G := F) (p := p) hA₀p with ⟨P, hA₀_le_P⟩
  have hP_norm : (P : Subgroup F).Normal := by
    have : Group.IsNilpotent F := by
      simpa [F] using section8FittingSubgroup_isNilpotent M
    exact Group.IsNilpotent.sylow_normal (G := F) (h := inferInstance) p P
  have hP_le_pCore : (P : Subgroup F) ≤ pCore p F :=
    le_sSup
      (show (P : Subgroup F) ∈
          {K : Subgroup F | K.Normal ∧ IsPGroup p K} from
        ⟨hP_norm, P.isPGroup'⟩)
  intro y hyY
  refine Subgroup.mem_map.mpr ?_
  refine ⟨⟨y, hY_le_F hyY⟩, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a haA₀
  have ha_pCore_map : (a : G) ∈ (pCore p F).map F.subtype := by
    exact Subgroup.mem_map.mpr ⟨a, hP_le_pCore (hA₀_le_P haA₀), rfl⟩
  have hcommG :=
    Subgroup.mem_centralizer_iff.mp (hY_cent_pCore hyY) (a : G) ha_pCore_map
  exact Subtype.ext hcommG

/-- The Fitting subgroup of `O_{p'}(M)` lies in `O_{p'}(F(M))`, with both
subgroups transported to the ambient group. -/
public theorem CFSG.section8_fittingSubgroupOf_pPrimeCore_le_piCoreIn_singleton_compl_fitting
    [Finite G] {p : ℕ} [Fact p.Prime] (M : Subgroup G) :
    (fittingSubgroupOf (G := M) (pPrimeCore p M)).map M.subtype ≤
      piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ (section8FittingSubgroup M) := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let F : Subgroup G := section8FittingSubgroup M
  let OpM_G : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ M
  let L_M : Subgroup M := fittingSubgroupOf (G := M) (pPrimeCore p M)
  let L_G : Subgroup G := L_M.map M.subtype
  have hL_le_F : L_G ≤ F := by
    have hL_le_fitM : L_M ≤ fittingSubgroup M :=
      fittingSubgroupOf_le_fittingSubgroup (G := M) (pPrimeCore p M) inferInstance
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxL, rfl⟩
    change (xM : G) ∈ F
    refine Subgroup.mem_map.mpr ?_
    exact ⟨xM, hL_le_fitM hxL, rfl⟩
  have hL_le_OpM : L_G ≤ OpM_G := by
    have hL_le_core : L_M ≤ pPrimeCore p M :=
      fittingSubgroupOf_le (G := M) (pPrimeCore p M)
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxL, rfl⟩
    have hxMap : (xM : G) ∈ (pPrimeCore p M).map M.subtype :=
      Subgroup.mem_map_of_mem M.subtype (hL_le_core hxL)
    simpa [OpM_G, p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hxMap
  have hLπ :
      IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ L_G := by
    have hOpMπ : IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ OpM_G := by
      simpa [OpM_G, p₀] using
        piCoreIn_isPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ M
    intro q hq
    exact hOpMπ q (hq.trans (Subgroup.card_dvd_of_le hL_le_OpM))
  have hL_norm_F : (L_G.subgroupOf F).Normal := by
    have hL_norm_M : L_M.Normal :=
      fittingSubgroupOf_normal (G := M) (pPrimeCore p M) inferInstance
    have hF_le_M : F ≤ M := section8FittingSubgroup_le M
    have hF_norm_LG : F ≤ Subgroup.normalizer (L_G : Set G) := by
      intro x hxF
      refine Subgroup.mem_normalizer_fintype ?_
      intro y hyL
      rcases Subgroup.mem_map.mp hyL with ⟨yM, hyLM, rfl⟩
      let xM : M := ⟨x, hF_le_M hxF⟩
      have hconjM : xM * yM * xM⁻¹ ∈ L_M :=
        hL_norm_M.conj_mem yM hyLM xM
      exact Subgroup.mem_map.mpr ⟨xM * yM * xM⁻¹, hconjM, by simp [xM, mul_assoc]⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hL_le_F).mpr hF_norm_LG
  exact
    section8_le_piCoreIn_of_normal_isPiSubgroup
      hL_le_F hL_norm_F hLπ

/-- The `q`-part of `F(N)` centralizes every subgroup contained in `O_{q'}(N)`. -/
public theorem CFSG.section8_piCoreIn_singleton_fitting_le_centralizer_of_le_singleton_compl_core
    [Finite G] (N Y : Subgroup G) (q : Nat.Primes)
    (hY_le : Y ≤ piCoreIn ({q} : Set Nat.Primes)ᶜ N) :
    piCoreIn ({q} : Set Nat.Primes) (section8FittingSubgroup N) ≤
      Subgroup.centralizer (Y : Set G) := by
  classical
  let FN : Subgroup G := section8FittingSubgroup N
  let Dq : Subgroup G := piCoreIn ({q} : Set Nat.Primes) FN
  let Cq : Subgroup G := piCoreIn ({q} : Set Nat.Primes)ᶜ N
  have hDq_le_N : Dq ≤ N := by
    have hDq_le_FN : Dq ≤ FN := by
      simpa [Dq, FN] using
        piCoreIn_le (G := G) ({q} : Set Nat.Primes) (section8FittingSubgroup N)
    exact hDq_le_FN.trans (by simpa [FN] using section8FittingSubgroup_le N)
  have hCq_le_N : Cq ≤ N := by
    simpa [Cq] using piCoreIn_le (G := G) ({q} : Set Nat.Primes)ᶜ N
  have hN_norm_FN : N ≤ Subgroup.normalizer (FN : Set G) := by
    have hFN_norm : (FN.subgroupOf N).Normal := by
      simpa [FN] using section8FittingSubgroup_normal_in N
    let : (FN.subgroupOf N).Normal := hFN_norm
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (by simpa [FN] using section8FittingSubgroup_le N)
  have hN_norm_Dq : N ≤ Subgroup.normalizer (Dq : Set G) := by
    simpa [Dq, FN] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({q} : Set Nat.Primes)) (H := FN) (P := N) hN_norm_FN
  have hDq_norm_N : (Dq.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDq_le_N).mpr hN_norm_Dq
  have hCq_norm_N : (Cq.subgroupOf N).Normal := by
    have hsub_eq : Cq.subgroupOf N = piCore ({q} : Set Nat.Primes)ᶜ N := by
      simpa [Cq] using piCore_map_subtype_subgroupOf (G := G) ({q} : Set Nat.Primes)ᶜ N
    rw [hsub_eq]
    infer_instance
  have hDqπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Dq := by
    simpa [Dq, FN] using
      piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes) (section8FittingSubgroup N)
  have hCqπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ Cq := by
    simpa [Cq] using piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ N
  have hDqNπ : IsPiSubgroup (G := N) ({q} : Set Nat.Primes) (Dq.subgroupOf N) := by
    intro s hs
    have hcard : Nat.card (Dq.subgroupOf N) = Nat.card Dq :=
      natCard_subgroupOf_eq _ _ hDq_le_N
    exact hDqπ s (by simpa [hcard] using hs)
  have hCqNπ : IsPiSubgroup (G := N) ({q} : Set Nat.Primes)ᶜ (Cq.subgroupOf N) := by
    intro s hs
    have hcard : Nat.card (Cq.subgroupOf N) = Nat.card Cq :=
      natCard_subgroupOf_eq _ _ hCq_le_N
    exact hCqπ s (by simpa [hcard] using hs)
  have hDqCq_inf_bot : Dq.subgroupOf N ⊓ Cq.subgroupOf N = ⊥ := by
    exact
      section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
        (G := N) (π := ({q} : Set Nat.Primes))
        (H := Dq.subgroupOf N ⊓ Cq.subgroupOf N)
        (Y := Cq.subgroupOf N) (C := Dq.subgroupOf N)
        inf_le_right inf_le_left hCqNπ hDqNπ
  intro d hdDq
  rw [Subgroup.mem_centralizer_iff]
  intro y hyY
  let dN : N := ⟨d, hDq_le_N hdDq⟩
  let yN : N := ⟨y, hCq_le_N (hY_le hyY)⟩
  have hdN : dN ∈ Dq.subgroupOf N := by
    change d ∈ Dq
    exact hdDq
  have hyN : yN ∈ Cq.subgroupOf N := by
    change y ∈ Cq
    exact hY_le hyY
  let : (Dq.subgroupOf N).Normal := hDq_norm_N
  let : (Cq.subgroupOf N).Normal := hCq_norm_N
  have hcomm_mem :
      ⁅dN, yN⁆ ∈ ⁅Dq.subgroupOf N, Cq.subgroupOf N⁆ :=
    Subgroup.commutator_mem_commutator hdN hyN
  have hcomm_inf : ⁅dN, yN⁆ ∈ Dq.subgroupOf N ⊓ Cq.subgroupOf N :=
    Subgroup.commutator_le_inf (H₁ := Dq.subgroupOf N) (H₂ := Cq.subgroupOf N)
      hcomm_mem
  have hcomm_bot : ⁅dN, yN⁆ ∈ (⊥ : Subgroup N) := by
    simpa [hDqCq_inf_bot] using hcomm_inf
  have hcomm_one_N : ⁅dN, yN⁆ = 1 := by
    simpa using hcomm_bot
  have hcomm_one_G : ⁅d, y⁆ = (1 : G) := by
    have hval := congrArg Subtype.val hcomm_one_N
    change ((↑(⁅dN, yN⁆) : G) = 1) at hval
    simpa [dN, yN, commutatorElement_def] using hval
  have hmul_dy : d * y = y * d :=
    commutatorElement_eq_one_iff_mul_comm.mp hcomm_one_G
  exact hmul_dy.symm

/-- In a finite nilpotent overgroup, every transported `q`-subgroup lies in the
singleton `π`-core. -/
public theorem CFSG.section8_isPGroup_le_piCoreIn_singleton_of_le_nilpotent
    [Finite G] {H K : Subgroup G} (hHK : H ≤ K) (q : Nat.Primes)
    (hHq : IsPGroup q.val H) [Group.IsNilpotent K] :
    H ≤ piCoreIn ({q} : Set Nat.Primes) K := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let Hsub : Subgroup K := H.subgroupOf K
  have hHsubq : IsPGroup q.val Hsub :=
    hHq.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm
  rcases IsPGroup.exists_le_sylow (G := K) (p := q.val) hHsubq with
    ⟨Q, hHsub_le_Q⟩
  have hQnorm : (Q : Subgroup K).Normal :=
    Group.IsNilpotent.sylow_normal (G := K) (h := inferInstance) q.val Q
  have hQ_le_pCore : (Q : Subgroup K) ≤ pCore q.val K :=
    le_sSup
      (show (Q : Subgroup K) ∈
          {L : Subgroup K | L.Normal ∧ IsPGroup q.val L} from
        ⟨hQnorm, Q.isPGroup'⟩)
  intro x hxH
  let xK : K := ⟨x, hHK hxH⟩
  have hxHsub : xK ∈ Hsub := by
    change x ∈ H
    exact hxH
  have hxCore : xK ∈ pCore q.val K :=
    hQ_le_pCore (hHsub_le_Q hxHsub)
  have hxMap : x ∈ (pCore q.val K).map K.subtype :=
    Subgroup.mem_map.mpr ⟨xK, hxCore, rfl⟩
  simpa [section8_piCoreIn_singleton_eq_pCore_map q K] using hxMap

/-- If `q ≠ r`, the part of `O_r(F(M))` lying in a proper overgroup `X` of
`C_{F(M)}(A₀)` lies in `O_{q'}(X)`. -/
public theorem CFSG.section8_piCoreIn_singleton_fitting_inf_le_singleton_compl_core
    [Finite G] [IsMinCE G] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (A₀ : Subgroup (section8FittingSubgroup M))
    {X : Subgroup G}
    (hAX : section8CentralizerInFitting M A₀ ≤ X) (hXproper : X ≠ ⊤)
    {q r : Nat.Primes}
    (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (_hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M)) (hrq : r ≠ q) :
    piCoreIn ({r} : Set Nat.Primes) (section8FittingSubgroup M) ⊓ X ≤
      piCoreIn ({q} : Set Nat.Primes)ᶜ X := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let F : Subgroup G := section8FittingSubgroup M
  let Z : Subgroup G := section8CenterInFitting M
  let Rq : Subgroup G := piCoreIn ({q} : Set Nat.Primes) Z
  let Fr : Subgroup G := piCoreIn ({r} : Set Nat.Primes) F
  let K : Subgroup G := Fr ⊓ X
  have hRq_le_A : Rq ≤ section8CentralizerInFitting M A₀ := by
    simpa [Rq, Z] using
      section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ q
  have hRq_le_X : Rq ≤ X := hRq_le_A.trans hAX
  let C : Subgroup X := Subgroup.centralizer ((Rq.subgroupOf X) : Set X)
  have hRq_p : IsPGroup q.val Rq := by
    simpa [Rq, Z] using section8_piCoreIn_singleton_centerInFitting_isPGroup M q
  have hRqX_p : IsPGroup q.val (Rq.subgroupOf X) :=
    hRq_p.of_equiv (Subgroup.subgroupOfEquivOfLe hRq_le_X).symm
  have hsolvX : Group.IsSolvable X :=
    IsMinCE.proper_subgroups_solvable X (lt_top_iff_ne_top.mpr hXproper)
  have hcoreC_le_coreX :
      (pPrimeCore q.val C).map C.subtype ≤ pPrimeCore q.val X := by
    simpa [C] using
      (proposition_1_15_b (G := X) hsolvX q.val (Rq.subgroupOf X) hRqX_p)
  have hFr_le_F : Fr ≤ F := by
    simpa [Fr, F] using piCoreIn_le (G := G) ({r} : Set Nat.Primes) F
  have hK_le_X : K ≤ X := by
    simp [K]
  have hKX_le_C : K.subgroupOf X ≤ C := by
    intro x hxKX
    rw [Subgroup.mem_centralizer_iff]
    intro z hzRqX
    apply Subtype.ext
    have hxK : (x : G) ∈ K := by
      simpa [K, Subgroup.mem_subgroupOf] using hxKX
    have hxFr : (x : G) ∈ Fr := hxK.1
    have hxF : (x : G) ∈ F := hFr_le_F hxFr
    have hzRq : (z : G) ∈ Rq := by
      simpa [Subgroup.mem_subgroupOf] using hzRqX
    have hzZ : (z : G) ∈ Z :=
      piCoreIn_le (G := G) ({q} : Set Nat.Primes) Z hzRq
    exact (Subgroup.mem_centralizer_iff.mp hzZ.2 (x : G) hxF).symm
  have hnormRq_eq : Subgroup.normalizer (Rq : Set G) = M := by
    simpa [Rq, Z] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hqF
  have hC_le_M : ∀ c : X, c ∈ C → (c : G) ∈ M := by
    intro c hc
    have hc_norm : (c : G) ∈ Subgroup.normalizer (Rq : Set G) := by
      refine Subgroup.mem_normalizer_fintype ?_
      intro z hzRq
      have hzX : z ∈ X := hRq_le_X hzRq
      let zX : X := ⟨z, hzX⟩
      have hzRqX : zX ∈ Rq.subgroupOf X := by
        simpa [zX, Subgroup.mem_subgroupOf] using hzRq
      have hcommX := Subgroup.mem_centralizer_iff.mp hc zX hzRqX
      have hcommG : z * (c : G) = (c : G) * z := congrArg Subtype.val hcommX
      have hconj : (c : G) * z * (c : G)⁻¹ = z := by
        calc
          (c : G) * z * (c : G)⁻¹ = (z * (c : G)) * (c : G)⁻¹ := by
            rw [← hcommG]
          _ = z := by simp [mul_assoc]
      simpa [hconj] using hzRq
    simpa [hnormRq_eq] using hc_norm
  have hM_norm_F : M ≤ Subgroup.normalizer (F : Set G) := by
    have hFNorm : (F.subgroupOf M).Normal := by
      simpa [F] using section8FittingSubgroup_normal_in M
    let : (F.subgroupOf M).Normal := hFNorm
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (by simpa [F] using section8FittingSubgroup_le M)
  have hM_norm_Fr : M ≤ Subgroup.normalizer (Fr : Set G) := by
    simpa [Fr, F] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({r} : Set Nat.Primes)) (H := F) (P := M) hM_norm_F
  have hC_norm_KX : C ≤ Subgroup.normalizer ((K.subgroupOf X : Subgroup X) : Set X) := by
    intro c hc
    have hcM : (c : G) ∈ M := hC_le_M c hc
    have hcNormFr : (c : G) ∈ Subgroup.normalizer (Fr : Set G) := hM_norm_Fr hcM
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hyK
    have hyK_G : (y : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf] using hyK
    have hyFr : (y : G) ∈ Fr := hyK_G.1
    have hconjFr : (c : G) * (y : G) * (c : G)⁻¹ ∈ Fr :=
      (Subgroup.mem_normalizer_iff.mp hcNormFr (y : G)).1 hyFr
    change ((c * y * c⁻¹ : X) : G) ∈ K
    exact ⟨by simpa using hconjFr, (c * y * c⁻¹ : X).property⟩
  have hKX_norm_C : ((K.subgroupOf X).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX_le_C).mpr hC_norm_KX
  have hFr_r : IsPGroup r.val Fr := by
    exact
      section8_isPGroup_of_isPiSubgroup_singleton
        (piCoreIn_isPiSubgroup (G := G) ({r} : Set Nat.Primes) F)
  have hK_r : IsPGroup r.val K := by
    simpa [K] using hFr_r.to_inf_left (K := X)
  have hcard_KC :
      Nat.card ((K.subgroupOf X).subgroupOf C) = Nat.card K := by
    calc
      Nat.card ((K.subgroupOf X).subgroupOf C) = Nat.card (K.subgroupOf X) :=
        natCard_subgroupOf_eq (K.subgroupOf X) C hKX_le_C
      _ = Nat.card K :=
        natCard_subgroupOf_eq K X hK_le_X
  have hcopK : Nat.Coprime q.val (Nat.card K) :=
    section8_coprime_prime_card_of_isPGroup_ne
      (G := G) (R := K) (q := q) (r := r) (by
        intro hqr
        exact hrq hqr.symm) hK_r
  have hcopKC : Nat.Coprime q.val (Nat.card ((K.subgroupOf X).subgroupOf C)) := by
    simpa [hcard_KC] using hcopK
  have hKC_le_core : (K.subgroupOf X).subgroupOf C ≤ pPrimeCore q.val C :=
    le_sSup
      (show (K.subgroupOf X).subgroupOf C ∈
          {L : Subgroup C | L.Normal ∧ Nat.Coprime q.val (Nat.card L)} from
        ⟨hKX_norm_C, hcopKC⟩)
  intro x hxK
  have hxK' : x ∈ K := by
    simpa [K, Fr, F] using hxK
  let xX : X := ⟨x, hK_le_X hxK'⟩
  have hxKX : xX ∈ K.subgroupOf X := by
    simpa [xX, Subgroup.mem_subgroupOf] using hxK'
  have hxC : xX ∈ C := hKX_le_C hxKX
  let xC : C := ⟨xX, hxC⟩
  have hxCoreC : xC ∈ pPrimeCore q.val C :=
    hKC_le_core (by simpa [xC, Subgroup.mem_subgroupOf] using hxKX)
  have hxCoreX : (xC : X) ∈ pPrimeCore q.val X :=
    hcoreC_le_coreX (Subgroup.mem_map_of_mem C.subtype hxCoreC)
  have hxCoreG : x ∈ (pPrimeCore q.val X).map X.subtype :=
    Subgroup.mem_map.mpr ⟨(xC : X), hxCoreX, rfl⟩
  have hq_cast : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := Subtype.ext rfl
  have hsingleton :
      ({q} : Set Nat.Primes) =
        ({(⟨q.val, Fact.out⟩ : Nat.Primes)} : Set Nat.Primes) := by
    exact congrArg (fun t : Nat.Primes => ({t} : Set Nat.Primes)) hq_cast.symm
  rw [hsingleton]
  have hcore_eq :=
    section8_piCoreIn_singleton_compl_eq_pPrimeCore_map (G := G) (p := q.val) X
  exact (hcore_eq.symm ▸ hxCoreG)

/-- The `p'`-core of `F(M)` lies in the `p'`-core of any maximal overgroup of
`C_{F(M)}(A₀)`. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_fitting_le_singleton_compl_maximalOver
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ (section8FittingSubgroup M) ≤
      piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ N := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let F : Subgroup G := section8FittingSubgroup M
  let Y : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ F
  let K : Subgroup Y := (piCoreIn ({p₀} : Set Nat.Primes)ᶜ N).comap Y.subtype
  have hY_le_F : Y ≤ F := by
    simpa [Y, F] using
      piCoreIn_le (G := G) ({p₀} : Set Nat.Primes)ᶜ (section8FittingSubgroup M)
  have hY_le_A : Y ≤ section8CentralizerInFitting M A₀ := by
    simpa [Y, F, p₀] using
      section8_piCoreIn_singleton_compl_fitting_le_centralizerInFitting M hA₀
  have hY_le_N : Y ≤ N := hY_le_A.trans hN.2
  have hnilF : Group.IsNilpotent F := by
    simpa [F] using section8FittingSubgroup_isNilpotent M
  let : Group.IsNilpotent F := hnilF
  have hnilY : Group.IsNilpotent Y := by
    have hYsub_nil : Group.IsNilpotent (Y.subgroupOf F) := by infer_instance
    let e : Y.subgroupOf F ≃* Y := Subgroup.subgroupOfEquivOfLe hY_le_F
    exact Group.nilpotent_of_mulEquiv (G := Y.subgroupOf F) (G' := Y) e
  let : Group.IsNilpotent Y := hnilY
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup Y) := by
    let e : Y ≃* (⊤ : Subgroup Y) :=
      (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).symm
    exact Group.nilpotent_of_mulEquiv (G := Y) (G' := (⊤ : Subgroup Y)) e
  have htop_le_sup :
      (⊤ : Subgroup Y) ≤
        ⨆ q : (Nat.card Y).primeFactors.attach, pCore q.1.1 Y :=
    normal_nilpotent_le_sup_pCore
      (G := Y) (N := (⊤ : Subgroup Y)) (hN := inferInstance) htop_nil
  have hF_norm_Y : F ≤ Subgroup.normalizer (Y : Set G) := by
    simpa [Y, F] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({p₀} : Set Nat.Primes)ᶜ)
        (H := F) (P := F) (Subgroup.le_normalizer)
  have hYπ : IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ Y := by
    simpa [Y, F] using
      piCoreIn_isPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ
        (section8FittingSubgroup M)
  have hsup_le_K :
      (⨆ q : (Nat.card Y).primeFactors.attach, pCore q.1.1 Y) ≤ K := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    have : Fact q.val.Prime := ⟨q.2⟩
    have hqY : q ∈ subgroupPrimeSet Y :=
      Nat.dvd_of_mem_primeFactors q0.1.2
    have hq_ne_p : q ≠ p₀ := by
      have hq_compl : q ∈ ({p₀} : Set Nat.Primes)ᶜ := hYπ q hqY
      intro hqp
      exact hq_compl (by simp [hqp])
    have hqF : q ∈ subgroupPrimeSet F :=
      section8_subgroupPrimeSet_mono hY_le_F hqY
    intro x hx
    change ((x : Y) : G) ∈ piCoreIn ({p₀} : Set Nat.Primes)ᶜ N
    have hxYcore : ((x : Y) : G) ∈ piCoreIn ({q} : Set Nat.Primes) Y := by
      have hxmap : ((x : Y) : G) ∈ (pCore q.val Y).map Y.subtype :=
        Subgroup.mem_map_of_mem Y.subtype (by simpa [q] using hx)
      simpa [section8_piCoreIn_singleton_eq_pCore_map q Y] using hxmap
    have hxFcore : ((x : Y) : G) ∈ piCoreIn ({q} : Set Nat.Primes) F :=
      section8_piCoreIn_singleton_le_of_le_normalizer hY_le_F hF_norm_Y q hxYcore
    have hxN : ((x : Y) : G) ∈ N := hY_le_N x.property
    have hxInf : ((x : Y) : G) ∈ piCoreIn ({q} : Set Nat.Primes) F ⊓ N :=
      ⟨hxFcore, hxN⟩
    exact
      section8_piCoreIn_singleton_fitting_inf_le_singleton_compl_core
        hM A₀ hN.2 hN.1.1 hpF hqF hq_ne_p hxInf
  intro x hxY
  let xY : Y := ⟨x, hxY⟩
  have hxK : xY ∈ K := by
    have hxTop : xY ∈ (⊤ : Subgroup Y) := Subgroup.mem_top xY
    exact hsup_le_K (htop_le_sup hxTop)
  exact hxK

/-- Equation (8.8): for a maximal overgroup `N` of `C_{F(M)}(A₀)`, the `p'`-core
of `N` is contained in the `p'`-core of the original maximal subgroup `M`. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_maximalOver_le_singleton_compl_original
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ N ≤
      piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ M := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let FN : Subgroup G := section8FittingSubgroup N
  let Dp : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes) FN
  let OpN_G : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ N
  have hσeq :
      subgroupPrimeSet FN = subgroupPrimeSet A := by
    simpa [FN, A] using
      section8FittingSubgroup_primeSet_eq_centralizerInFitting_of_maximalOver
        hM hpF hA₀ hA₀rank hHyp hN
  have hAπF : subgroupPrimeSet A = subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [A] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hpA : p₀ ∈ subgroupPrimeSet A := by
    simpa [A, hAπF, p₀] using hpF
  have hpFN : p₀ ∈ subgroupPrimeSet FN := by
    simpa [hσeq] using hpA
  have hFN_le_M : FN ≤ M :=
    section8FittingSubgroup_maximalOver_le_original
      hM hpF hA₀ hA₀rank hnFp hHyp hN
  have hDp_le_FN : Dp ≤ FN := by
    simpa [Dp, FN] using
      piCoreIn_le (G := G) ({p₀} : Set Nat.Primes) (section8FittingSubgroup N)
  have hDp_le_N : Dp ≤ N :=
    hDp_le_FN.trans (by simpa [FN] using section8FittingSubgroup_le N)
  have hDp_le_M : Dp ≤ M := hDp_le_FN.trans hFN_le_M
  have hnilFN : Group.IsNilpotent FN := by
    simpa [FN] using section8FittingSubgroup_isNilpotent N
  have hDp_ne_bot : Dp ≠ ⊥ := by
    let : Group.IsNilpotent FN := hnilFN
    simpa [Dp, FN, p₀] using
      section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isNilpotent
        (H := FN) hpFN
  have hN_norm_FN : N ≤ Subgroup.normalizer (FN : Set G) := by
    have hFN_norm : (FN.subgroupOf N).Normal := by
      simpa [FN] using section8FittingSubgroup_normal_in N
    let : (FN.subgroupOf N).Normal := hFN_norm
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (by simpa [FN] using section8FittingSubgroup_le N)
  have hN_norm_Dp : N ≤ Subgroup.normalizer (Dp : Set G) := by
    simpa [Dp, FN] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({p₀} : Set Nat.Primes)) (H := FN) (P := N) hN_norm_FN
  have hDp_norm_N : (Dp.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDp_le_N).mpr hN_norm_Dp
  have hnorm_Dp_eq_N : Subgroup.normalizer (Dp : Set G) = N :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      hN.1 hDp_le_N hDp_ne_bot hDp_norm_N
  let DpM : Subgroup M := Dp.subgroupOf M
  let C : Subgroup M := Subgroup.centralizer (DpM : Set M)
  have hDp_p : IsPGroup p Dp := by
    simpa [Dp, FN, p₀] using
      section8_isPGroup_of_isPiSubgroup_singleton
        (piCoreIn_isPiSubgroup (G := G) ({p₀} : Set Nat.Primes) FN)
  have hDpM_p : IsPGroup p DpM :=
    hDp_p.of_equiv (Subgroup.subgroupOfEquivOfLe hDp_le_M).symm
  have hDpN_p : IsPGroup p (Dp.subgroupOf N) :=
    hDp_p.of_equiv (Subgroup.subgroupOfEquivOfLe hDp_le_N).symm
  have hC_le_N : ∀ c : M, c ∈ C → (c : G) ∈ N := by
    intro c hc
    have hc_norm : (c : G) ∈ Subgroup.normalizer (Dp : Set G) := by
      refine Subgroup.mem_normalizer_fintype ?_
      intro z hzDp
      let zM : M := ⟨z, hDp_le_M hzDp⟩
      have hzDpM : zM ∈ DpM := by
        simpa [DpM, zM, Subgroup.mem_subgroupOf] using hzDp
      have hcommM := Subgroup.mem_centralizer_iff.mp hc zM hzDpM
      have hcommG : z * (c : G) = (c : G) * z := congrArg Subtype.val hcommM
      have hconj : (c : G) * z * (c : G)⁻¹ = z := by
        calc
          (c : G) * z * (c : G)⁻¹ = (z * (c : G)) * (c : G)⁻¹ := by
            rw [← hcommG]
          _ = z := by simp [mul_assoc]
      simpa [hconj] using hzDp
    simpa [hnorm_Dp_eq_N] using hc_norm
  have hOpN_le_M : OpN_G ≤ M := by
    simpa [OpN_G, p₀] using
      section8_piCoreIn_singleton_compl_maximalOver_le_original
        hM hpF hA₀ hA₀rank hHyp hN
  have hOpN_le_C : OpN_G.subgroupOf M ≤ C := by
    let : (Dp.subgroupOf N).Normal := hDp_norm_N
    have hcentN :
        pPrimeCore p N ≤ Subgroup.centralizer (Dp.subgroupOf N : Set N) :=
      pPrimeCore_le_centralizer_of_normal_pgroup
        (G := N) p (Dp.subgroupOf N) hDpN_p
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hzDpM
    have hxOpN : (x : G) ∈ OpN_G := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxMap : (x : G) ∈ (pPrimeCore p N).map N.subtype := by
      simpa [OpN_G, p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hxOpN
    rcases Subgroup.mem_map.mp hxMap with ⟨xN, hxCoreN, hxN_eq⟩
    let zN : N := ⟨(z : G), hDp_le_N (by simpa [DpM, Subgroup.mem_subgroupOf] using hzDpM)⟩
    have hzDpN : zN ∈ Dp.subgroupOf N := by
      simpa [zN, DpM, Subgroup.mem_subgroupOf] using hzDpM
    have hcommN := Subgroup.mem_centralizer_iff.mp (hcentN hxCoreN) zN hzDpN
    have hxN_eq' : (xN : G) = (x : G) := hxN_eq
    apply Subtype.ext
    calc
      (z : G) * (x : G) = (zN : G) * (xN : G) := by simp [zN, hxN_eq']
      _ = (xN : G) * (zN : G) := congrArg Subtype.val hcommN
      _ = (x : G) * (z : G) := by simp [zN, hxN_eq']
  have hN_norm_OpN : N ≤ Subgroup.normalizer (OpN_G : Set G) := by
    simpa [OpN_G] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({p₀} : Set Nat.Primes)ᶜ) (H := N) (P := N) (Subgroup.le_normalizer)
  have hC_norm_OpN :
      C ≤ Subgroup.normalizer ((OpN_G.subgroupOf M : Subgroup M) : Set M) := by
    intro c hc
    have hcNormG : (c : G) ∈ Subgroup.normalizer (OpN_G : Set G) :=
      hN_norm_OpN (hC_le_N c hc)
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hy
    have hyG : (y : G) ∈ OpN_G := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hconjG : (c : G) * (y : G) * (c : G)⁻¹ ∈ OpN_G :=
      (Subgroup.mem_normalizer_iff.mp hcNormG (y : G)).1 hyG
    change ((c * y * c⁻¹ : M) : G) ∈ OpN_G
    simpa using hconjG
  have hOpNC_norm : ((OpN_G.subgroupOf M).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOpN_le_C).mpr hC_norm_OpN
  have hOpNCπ :
      IsPiSubgroup (G := C) ({p₀} : Set Nat.Primes)ᶜ
        ((OpN_G.subgroupOf M).subgroupOf C) := by
    have hOpNπ : IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ OpN_G := by
      simpa [OpN_G] using
        piCoreIn_isPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ N
    intro q hq
    have hcardC :
        Nat.card ((OpN_G.subgroupOf M).subgroupOf C) =
          Nat.card (OpN_G.subgroupOf M) :=
      natCard_subgroupOf_eq _ _ hOpN_le_C
    have hcardM : Nat.card (OpN_G.subgroupOf M) = Nat.card OpN_G :=
      natCard_subgroupOf_eq _ _ hOpN_le_M
    exact hOpNπ q (by simpa [hcardC, hcardM] using hq)
  have hOpNC_cop : Nat.Coprime p (Nat.card ((OpN_G.subgroupOf M).subgroupOf C)) := by
    refine (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr ?_
    intro hpdiv
    have hp_mem : p₀ ∈ ({p₀} : Set Nat.Primes)ᶜ :=
      hOpNCπ p₀ (by simpa [p₀] using hpdiv)
    exact hp_mem (Set.mem_singleton p₀)
  have hOpNC_le_coreC : (OpN_G.subgroupOf M).subgroupOf C ≤ pPrimeCore p C :=
    le_sSup
      (show (OpN_G.subgroupOf M).subgroupOf C ∈
          {L : Subgroup C | L.Normal ∧ Nat.Coprime p (Nat.card L)} from
        ⟨hOpNC_norm, hOpNC_cop⟩)
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hcoreC_le_coreM :
      (pPrimeCore p C).map C.subtype ≤ pPrimeCore p M := by
    simpa [C, DpM] using
      (proposition_1_15_b (G := M) hMsolv p DpM hDpM_p)
  intro x hxOpN
  let xM : M := ⟨x, hOpN_le_M hxOpN⟩
  have hxOpNM : xM ∈ OpN_G.subgroupOf M := by
    simpa [xM, Subgroup.mem_subgroupOf] using hxOpN
  have hxC : xM ∈ C := hOpN_le_C hxOpNM
  let xC : C := ⟨xM, hxC⟩
  have hxOpNC : xC ∈ (OpN_G.subgroupOf M).subgroupOf C := by
    simpa [xC, Subgroup.mem_subgroupOf] using hxOpNM
  have hxCoreC : xC ∈ pPrimeCore p C := hOpNC_le_coreC hxOpNC
  have hxCoreM : (xC : M) ∈ pPrimeCore p M :=
    hcoreC_le_coreM (Subgroup.mem_map_of_mem C.subtype hxCoreC)
  have hxMapG : x ∈ (pPrimeCore p M).map M.subtype :=
    Subgroup.mem_map.mpr ⟨(xC : M), hxCoreM, rfl⟩
  simpa [p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hxMapG

/-- The `p'`-core of the original maximal subgroup lies in any maximal overgroup of
`C_{F(M)}(A₀)`. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_original_le_maximalOver
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ M ≤ N := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let A : Subgroup G := section8CentralizerInFitting M A₀
  let F : Subgroup G := section8FittingSubgroup M
  let FN : Subgroup G := section8FittingSubgroup N
  let Dp : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes) FN
  let OpF : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ F
  let OpM_G : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ M
  have hσeq :
      subgroupPrimeSet FN = subgroupPrimeSet A := by
    simpa [FN, A] using
      section8FittingSubgroup_primeSet_eq_centralizerInFitting_of_maximalOver
        hM hpF hA₀ hA₀rank hHyp hN
  have hAπF : subgroupPrimeSet A = subgroupPrimeSet (section8FittingSubgroup M) := by
    simpa [A] using section8CentralizerInFitting_primeSet_eq_fitting M A₀
  have hpA : p₀ ∈ subgroupPrimeSet A := by
    simpa [A, hAπF, p₀] using hpF
  have hpFN : p₀ ∈ subgroupPrimeSet FN := by
    simpa [hσeq] using hpA
  have hDp_le_FN : Dp ≤ FN := by
    simpa [Dp, FN] using
      piCoreIn_le (G := G) ({p₀} : Set Nat.Primes) (section8FittingSubgroup N)
  have hDp_le_N : Dp ≤ N :=
    hDp_le_FN.trans (by simpa [FN] using section8FittingSubgroup_le N)
  have hFN_le_M : FN ≤ M :=
    section8FittingSubgroup_maximalOver_le_original
      hM hpF hA₀ hA₀rank hnFp hHyp hN
  have hDp_le_M : Dp ≤ M := hDp_le_FN.trans hFN_le_M
  have hnilFN : Group.IsNilpotent FN := by
    simpa [FN] using section8FittingSubgroup_isNilpotent N
  have hDp_ne_bot : Dp ≠ ⊥ := by
    let : Group.IsNilpotent FN := hnilFN
    simpa [Dp, FN, p₀] using
      section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isNilpotent
        (H := FN) hpFN
  have hN_norm_FN : N ≤ Subgroup.normalizer (FN : Set G) := by
    have hFN_norm : (FN.subgroupOf N).Normal := by
      simpa [FN] using section8FittingSubgroup_normal_in N
    let : (FN.subgroupOf N).Normal := hFN_norm
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (by simpa [FN] using section8FittingSubgroup_le N)
  have hN_norm_Dp : N ≤ Subgroup.normalizer (Dp : Set G) := by
    simpa [Dp, FN] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({p₀} : Set Nat.Primes)) (H := FN) (P := N) hN_norm_FN
  have hDp_norm_N : (Dp.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDp_le_N).mpr hN_norm_Dp
  have hnorm_Dp_eq_N : Subgroup.normalizer (Dp : Set G) = N :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      hN.1 hDp_le_N hDp_ne_bot hDp_norm_N
  have hOpF_le_OpN : OpF ≤ piCoreIn ({p₀} : Set Nat.Primes)ᶜ N := by
    simpa [OpF, F, p₀] using
      section8_piCoreIn_singleton_compl_fitting_le_singleton_compl_maximalOver
        hM hpF hA₀ hN
  have hDp_cent_OpF : Dp ≤ Subgroup.centralizer (OpF : Set G) := by
    simpa [Dp, FN, OpF, p₀] using
      section8_piCoreIn_singleton_fitting_le_centralizer_of_le_singleton_compl_core
        N OpF p₀ hOpF_le_OpN
  let DpM : Subgroup M := Dp.subgroupOf M
  have hDp_p : IsPGroup p Dp := by
    simpa [Dp, FN, p₀] using
      section8_isPGroup_of_isPiSubgroup_singleton
        (piCoreIn_isPiSubgroup (G := G) ({p₀} : Set Nat.Primes) FN)
  have hDpM_p : IsPGroup p DpM :=
    hDp_p.of_equiv (Subgroup.subgroupOfEquivOfLe hDp_le_M).symm
  have hDpM_norm_OpM : DpM ≤ Subgroup.normalizer (pPrimeCore p M : Set M) := by
    have hnorm_top : Subgroup.normalizer (pPrimeCore p M : Set M) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (pPrimeCore p M).Normal)
    rw [hnorm_top]
    exact le_top
  have hcop_DpM_OpM : Nat.Coprime (Nat.card DpM) (Nat.card (pPrimeCore p M)) := by
    rcases hDpM_p.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (pPrimeCore_coprime_card (G := M) (p := p)).pow_left n
  have hDpM_cent_fitOpM :
      DpM ≤ Subgroup.centralizer
        (fittingSubgroupOf (G := M) (pPrimeCore p M) : Set M) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hdG : (d : G) ∈ Dp := by
      simpa [DpM, Subgroup.mem_subgroupOf] using hd
    have hfG : (f : G) ∈ OpF := by
      have hfMap : (f : G) ∈
          (fittingSubgroupOf (G := M) (pPrimeCore p M)).map M.subtype :=
        Subgroup.mem_map_of_mem M.subtype hf
      exact
        section8_fittingSubgroupOf_pPrimeCore_le_piCoreIn_singleton_compl_fitting
          M hfMap
    have hcommG := Subgroup.mem_centralizer_iff.mp (hDp_cent_OpF hdG) (f : G) hfG
    exact Subtype.ext hcommG
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  let : Group.IsSolvable M := hMsolv
  have hOpMsolv : Group.IsSolvable (pPrimeCore p M) := by infer_instance
  have hDpM_cent_OpM : DpM ≤ Subgroup.centralizer (pPrimeCore p M : Set M) :=
    section8_le_centralizer_of_le_centralizer_fitting_of_coprime
      hOpMsolv hDpM_norm_OpM hcop_DpM_OpM hDpM_cent_fitOpM
  intro x hxOpM
  have hxMap : x ∈ (pPrimeCore p M).map M.subtype := by
    simpa [OpM_G, p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hxOpM
  rcases Subgroup.mem_map.mp hxMap with ⟨xM, hxCoreM, hxM_eq⟩
  have hx_cent_Dp : x ∈ Subgroup.centralizer (Dp : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hdDp
    let dM : M := ⟨d, hDp_le_M hdDp⟩
    have hdDpM : dM ∈ DpM := by
      simpa [dM, DpM, Subgroup.mem_subgroupOf] using hdDp
    have hcommM := Subgroup.mem_centralizer_iff.mp (hDpM_cent_OpM hdDpM) xM hxCoreM
    have hxM_eq' : (xM : G) = x := hxM_eq
    calc
      d * x = (dM : G) * (xM : G) := by simp [dM, hxM_eq']
      _ = (xM : G) * (dM : G) := by
        exact (congrArg Subtype.val hcommM).symm
      _ = x * d := by simp [dM, hxM_eq']
  have hx_norm_Dp : x ∈ Subgroup.normalizer (Dp : Set G) :=
    centralizer_le_normalizer Dp hx_cent_Dp
  simpa [hnorm_Dp_eq_N] using hx_norm_Dp

/-- The reverse containment to (8.8): the `p'`-core of the original maximal subgroup
lies in the `p'`-core of any maximal overgroup of `C_{F(M)}(A₀)`. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_original_le_singleton_compl_maximalOver
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    (hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ M ≤
      piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ N := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let Z : Subgroup G := section8CenterInFitting M
  let Rp : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes) Z
  let OpM_G : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ M
  have hRp_le_A : Rp ≤ section8CentralizerInFitting M A₀ := by
    simpa [Rp, Z, p₀] using
      section8_piCoreIn_singleton_centerInFitting_le_centralizerInFitting M A₀ p₀
  have hRp_le_N : Rp ≤ N := hRp_le_A.trans hN.2
  have hRp_le_M : Rp ≤ M :=
    (piCoreIn_le (G := G) ({p₀} : Set Nat.Primes) Z).trans
      (by simpa [Z] using section8CenterInFitting_le_maximal M)
  have hnorm_Rp_eq_M : Subgroup.normalizer (Rp : Set G) = M := by
    simpa [Rp, Z, p₀] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hpF
  have hRp_p : IsPGroup p Rp := by
    simpa [Rp, Z, p₀] using section8_piCoreIn_singleton_centerInFitting_isPGroup M p₀
  have hRpN_p : IsPGroup p (Rp.subgroupOf N) :=
    hRp_p.of_equiv (Subgroup.subgroupOfEquivOfLe hRp_le_N).symm
  have hRpM_p : IsPGroup p (Rp.subgroupOf M) :=
    hRp_p.of_equiv (Subgroup.subgroupOfEquivOfLe hRp_le_M).symm
  have hM_norm_Rp : M ≤ Subgroup.normalizer (Rp : Set G) := by
    intro m hm
    simpa [hnorm_Rp_eq_M] using hm
  have hRp_norm_M : (Rp.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRp_le_M).mpr hM_norm_Rp
  have hOpM_le_N : OpM_G ≤ N := by
    simpa [OpM_G, p₀] using
      section8_piCoreIn_singleton_compl_original_le_maximalOver
        hM hpF hA₀ hA₀rank hnFp hHyp hN
  let RpN : Subgroup N := Rp.subgroupOf N
  let C : Subgroup N := Subgroup.centralizer (RpN : Set N)
  have hC_le_M : ∀ c : N, c ∈ C → (c : G) ∈ M := by
    intro c hc
    have hc_norm : (c : G) ∈ Subgroup.normalizer (Rp : Set G) := by
      refine Subgroup.mem_normalizer_fintype ?_
      intro z hzRp
      let zN : N := ⟨z, hRp_le_N hzRp⟩
      have hzRpN : zN ∈ RpN := by
        simpa [RpN, zN, Subgroup.mem_subgroupOf] using hzRp
      have hcommN := Subgroup.mem_centralizer_iff.mp hc zN hzRpN
      have hcommG : z * (c : G) = (c : G) * z := congrArg Subtype.val hcommN
      have hconj : (c : G) * z * (c : G)⁻¹ = z := by
        calc
          (c : G) * z * (c : G)⁻¹ = (z * (c : G)) * (c : G)⁻¹ := by
            rw [← hcommG]
          _ = z := by simp [mul_assoc]
      simpa [hconj] using hzRp
    simpa [hnorm_Rp_eq_M] using hc_norm
  have hOpM_le_C : OpM_G.subgroupOf N ≤ C := by
    let : (Rp.subgroupOf M).Normal := hRp_norm_M
    have hcentM :
        pPrimeCore p M ≤ Subgroup.centralizer (Rp.subgroupOf M : Set M) :=
      pPrimeCore_le_centralizer_of_normal_pgroup
        (G := M) p (Rp.subgroupOf M) hRpM_p
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hzRpN
    have hxOpM : (x : G) ∈ OpM_G := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxMap : (x : G) ∈ (pPrimeCore p M).map M.subtype := by
      simpa [OpM_G, p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hxOpM
    rcases Subgroup.mem_map.mp hxMap with ⟨xM, hxCoreM, hxM_eq⟩
    let zM : M := ⟨(z : G), hRp_le_M (by simpa [RpN, Subgroup.mem_subgroupOf] using hzRpN)⟩
    have hzRpM : zM ∈ Rp.subgroupOf M := by
      simpa [zM, RpN, Subgroup.mem_subgroupOf] using hzRpN
    have hcommM := Subgroup.mem_centralizer_iff.mp (hcentM hxCoreM) zM hzRpM
    have hxM_eq' : (xM : G) = (x : G) := hxM_eq
    apply Subtype.ext
    calc
      (z : G) * (x : G) = (zM : G) * (xM : G) := by simp [zM, hxM_eq']
      _ = (xM : G) * (zM : G) := congrArg Subtype.val hcommM
      _ = (x : G) * (z : G) := by simp [zM, hxM_eq']
  have hM_norm_OpM : M ≤ Subgroup.normalizer (OpM_G : Set G) := by
    simpa [OpM_G] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({p₀} : Set Nat.Primes)ᶜ) (H := M) (P := M) (Subgroup.le_normalizer)
  have hC_norm_OpM :
      C ≤ Subgroup.normalizer ((OpM_G.subgroupOf N : Subgroup N) : Set N) := by
    intro c hc
    have hcNormG : (c : G) ∈ Subgroup.normalizer (OpM_G : Set G) :=
      hM_norm_OpM (hC_le_M c hc)
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hy
    have hyG : (y : G) ∈ OpM_G := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hconjG : (c : G) * (y : G) * (c : G)⁻¹ ∈ OpM_G :=
      (Subgroup.mem_normalizer_iff.mp hcNormG (y : G)).1 hyG
    change ((c * y * c⁻¹ : N) : G) ∈ OpM_G
    simpa using hconjG
  have hOpMC_norm : ((OpM_G.subgroupOf N).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOpM_le_C).mpr hC_norm_OpM
  have hOpMCπ :
      IsPiSubgroup (G := C) ({p₀} : Set Nat.Primes)ᶜ
        ((OpM_G.subgroupOf N).subgroupOf C) := by
    have hOpMπ : IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ OpM_G := by
      simpa [OpM_G] using
        piCoreIn_isPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ M
    intro q hq
    have hcardC :
        Nat.card ((OpM_G.subgroupOf N).subgroupOf C) =
          Nat.card (OpM_G.subgroupOf N) :=
      natCard_subgroupOf_eq _ _ hOpM_le_C
    have hcardN : Nat.card (OpM_G.subgroupOf N) = Nat.card OpM_G :=
      natCard_subgroupOf_eq _ _ hOpM_le_N
    exact hOpMπ q (by simpa [hcardC, hcardN] using hq)
  have hOpMC_cop : Nat.Coprime p (Nat.card ((OpM_G.subgroupOf N).subgroupOf C)) := by
    refine (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr ?_
    intro hpdiv
    have hp_mem : p₀ ∈ ({p₀} : Set Nat.Primes)ᶜ :=
      hOpMCπ p₀ (by simpa [p₀] using hpdiv)
    exact hp_mem (Set.mem_singleton p₀)
  have hOpMC_le_coreC : (OpM_G.subgroupOf N).subgroupOf C ≤ pPrimeCore p C :=
    le_sSup
      (show (OpM_G.subgroupOf N).subgroupOf C ∈
          {L : Subgroup C | L.Normal ∧ Nat.Coprime p (Nat.card L)} from
        ⟨hOpMC_norm, hOpMC_cop⟩)
  have hNsolv : Group.IsSolvable N :=
    IsMinCE.proper_subgroups_solvable N (lt_top_iff_ne_top.mpr hN.1.1)
  have hcoreC_le_coreN :
      (pPrimeCore p C).map C.subtype ≤ pPrimeCore p N := by
    simpa [C, RpN] using
      (proposition_1_15_b (G := N) hNsolv p RpN hRpN_p)
  intro x hxOpM
  let xN : N := ⟨x, hOpM_le_N hxOpM⟩
  have hxOpMN : xN ∈ OpM_G.subgroupOf N := by
    simpa [xN, Subgroup.mem_subgroupOf] using hxOpM
  have hxC : xN ∈ C := hOpM_le_C hxOpMN
  let xC : C := ⟨xN, hxC⟩
  have hxOpMC : xC ∈ (OpM_G.subgroupOf N).subgroupOf C := by
    simpa [xC, Subgroup.mem_subgroupOf] using hxOpMN
  have hxCoreC : xC ∈ pPrimeCore p C := hOpMC_le_coreC hxOpMC
  have hxCoreN : (xC : N) ∈ pPrimeCore p N :=
    hcoreC_le_coreN (Subgroup.mem_map_of_mem C.subtype hxCoreC)
  have hxMapG : x ∈ (pPrimeCore p N).map N.subtype :=
    Subgroup.mem_map.mpr ⟨(xC : N), hxCoreN, rfl⟩
  simpa [p₀, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hxMapG

/-- In the non-`p` branch, the original maximal subgroup has nontrivial `p'`-core. -/
public theorem CFSG.section8_piCoreIn_singleton_compl_original_ne_bot_of_not_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M)) :
    piCoreIn ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ M ≠ ⊥ := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  rcases section8_exists_prime_ne_of_not_isPGroup
      (G := G) (H := section8FittingSubgroup M) hnFp with
    ⟨q, hqF, hq_ne_p⟩
  let Z : Subgroup G := section8CenterInFitting M
  let Rq : Subgroup G := piCoreIn ({q} : Set Nat.Primes) Z
  have hqZ : q ∈ subgroupPrimeSet Z := by
    have hZπ : subgroupPrimeSet Z = subgroupPrimeSet (section8FittingSubgroup M) := by
      simpa [Z] using section8CenterInFitting_primeSet_eq_fitting M
    simpa [hZπ] using hqF
  have : IsMulCommutative Z := by
    simpa [Z] using section8CenterInFitting_isMulCommutative M
  have hRq_ne_bot : Rq ≠ ⊥ := by
    simpa [Rq] using
      section8_piCoreIn_singleton_ne_bot_of_mem_subgroupPrimeSet_of_isMulCommutative
        (H := Z) hqZ
  have hRq_le_M : Rq ≤ M :=
    (piCoreIn_le (G := G) ({q} : Set Nat.Primes) Z).trans
      (by simpa [Z] using section8CenterInFitting_le_maximal M)
  have hnorm_Rq_eq_M : Subgroup.normalizer (Rq : Set G) = M := by
    simpa [Rq, Z] using section8_normalizer_piCoreIn_singleton_centerInFitting_eq hM hqF
  have hM_norm_Rq : M ≤ Subgroup.normalizer (Rq : Set G) := by
    intro m hm
    simpa [hnorm_Rq_eq_M] using hm
  have hRq_norm_M : (Rq.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRq_le_M).mpr hM_norm_Rq
  have hRq_q : IsPGroup q.val Rq := by
    simpa [Rq, Z] using section8_piCoreIn_singleton_centerInFitting_isPGroup M q
  have hRqπp : IsPiSubgroup (G := G) ({p₀} : Set Nat.Primes)ᶜ Rq := by
    have hRqπq : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Rq :=
      section8_isPiSubgroup_singleton_of_isPGroup hRq_q
    intro s hs
    have hs_eq_q : s = q := by
      simpa using hRqπq s hs
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hs_eq_p
    exact hq_ne_p (hs_eq_q.symm.trans hs_eq_p)
  have hRq_le_OpM :
      Rq ≤ piCoreIn ({p₀} : Set Nat.Primes)ᶜ M :=
    section8_le_piCoreIn_of_normal_isPiSubgroup
      hRq_le_M hRq_norm_M hRqπp
  intro hOpM_bot
  exact hRq_ne_bot (le_bot_iff.mp (hRq_le_OpM.trans (le_of_eq hOpM_bot)))

/-- Final maximal-overgroup endpoint for branch (a): every maximal overgroup of
`C_{F(M)}(A₀)` is the original maximal subgroup `M`. -/
public theorem CFSG.section8CentralizerInFitting_maximal_overgroups_eq
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    N = M := by
  classical
  let p₀ : Nat.Primes := ⟨p, Fact.out⟩
  let OpM : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ M
  let OpN : Subgroup G := piCoreIn ({p₀} : Set Nat.Primes)ᶜ N
  have hHyp : Hypothesis7_1 (section8CentralizerInFitting M A₀) :=
    section8CentralizerInFitting_Hypothesis7_1 hM hpF hA₀ hA₀rank hnFp
  have hOpN_le_OpM : OpN ≤ OpM := by
    simpa [OpN, OpM, p₀] using
      section8_piCoreIn_singleton_compl_maximalOver_le_singleton_compl_original
        hM hpF hA₀ hA₀rank hnFp hHyp hN
  have hOpM_le_OpN : OpM ≤ OpN := by
    simpa [OpN, OpM, p₀] using
      section8_piCoreIn_singleton_compl_original_le_singleton_compl_maximalOver
        hM hpF hA₀ hA₀rank hnFp hHyp hN
  have hOp_eq : OpN = OpM := le_antisymm hOpN_le_OpM hOpM_le_OpN
  have hOpM_ne_bot : OpM ≠ ⊥ := by
    simpa [OpM, p₀] using
      section8_piCoreIn_singleton_compl_original_ne_bot_of_not_isPGroup
        hM hnFp
  have hOpN_ne_bot : OpN ≠ ⊥ := by
    intro hOpN_bot
    have hOpM_bot : OpM = ⊥ := by
      simpa [hOp_eq] using hOpN_bot
    exact hOpM_ne_bot hOpM_bot
  have hOpM_le_M : OpM ≤ M := by
    simpa [OpM] using piCoreIn_le (G := G) ({p₀} : Set Nat.Primes)ᶜ M
  have hM_norm_OpM : M ≤ Subgroup.normalizer (OpM : Set G) := by
    simpa [OpM] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({p₀} : Set Nat.Primes)ᶜ) (H := M) (P := M) (Subgroup.le_normalizer)
  have hOpM_norm_M : (OpM.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOpM_le_M).mpr hM_norm_OpM
  have hnorm_OpM_eq_M : Subgroup.normalizer (OpM : Set G) = M :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      hM hOpM_le_M hOpM_ne_bot hOpM_norm_M
  have hOpN_le_N : OpN ≤ N := by
    simpa [OpN] using piCoreIn_le (G := G) ({p₀} : Set Nat.Primes)ᶜ N
  have hN_norm_OpN : N ≤ Subgroup.normalizer (OpN : Set G) := by
    simpa [OpN] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (π := ({p₀} : Set Nat.Primes)ᶜ) (H := N) (P := N) (Subgroup.le_normalizer)
  have hOpN_norm_N : (OpN.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOpN_le_N).mpr hN_norm_OpN
  have hnorm_OpN_eq_N : Subgroup.normalizer (OpN : Set G) = N :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      hN.1 hOpN_le_N hOpN_ne_bot hOpN_norm_N
  calc
    N = Subgroup.normalizer (OpN : Set G) := hnorm_OpN_eq_N.symm
    _ = Subgroup.normalizer (OpM : Set G) := by rw [hOp_eq]
    _ = M := hnorm_OpM_eq_M

/-- Normalizer-control form of the final branch-(a) endpoint. -/
public theorem CFSG.section8CentralizerInFitting_maximal_overgroups_le_normalizer_fitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀)) :
    N ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
  have hNM : N = M :=
    section8CentralizerInFitting_maximal_overgroups_eq
      hM hpF hA₀ hA₀rank hnFp hN
  rw [hNM]
  let : ((section8FittingSubgroup M).subgroupOf M).Normal :=
    section8FittingSubgroup_normal_in M
  exact Subgroup.le_normalizer_of_normal_subgroupOf (section8FittingSubgroup_le M)

/-- In branch (b), the `H_G^*(F(M);q)` family is subsingleton for `q ≠ p`. -/
public theorem CFSG.section8_HStarFamily_fitting_subsingleton_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩) :
    Subsingleton {Q : Subgroup G //
      Q ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
        ({q} : Set Nat.Primes)} := by
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  have hsubset :
      section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
          ({q} : Set Nat.Primes) ⊆
        section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes) := by
    simpa [A_G] using
      section8_HStarFamily_fitting_subset_sylowSubgroupInAmbient_of_fitting_isPGroup
        hM hpF hFp P hA hq
  have hsubA :
      Subsingleton {Q : Subgroup G //
        Q ∈ section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes)} := by
    simpa [A_G] using
      section8_HStarFamily_sylowSubgroupInAmbient_subsingleton_of_fitting_isPGroup
        hM hpF hFp P hA hq
  refine ⟨?_⟩
  intro Q₁ Q₂
  apply Subtype.ext
  have h₁ : (Q₁ : Subgroup G) ∈
      section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes) :=
    hsubset Q₁.property
  have h₂ : (Q₂ : Subgroup G) ∈
      section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes) :=
    hsubset Q₂.property
  have hEq :=
    Subsingleton.elim
      (⟨(Q₁ : Subgroup G), h₁⟩ :
        {Q : Subgroup G //
          Q ∈ section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes)})
      (⟨(Q₂ : Subgroup G), h₂⟩ :
        {Q : Subgroup G //
          Q ∈ section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes)})
  exact congrArg
    (fun R : {Q : Subgroup G //
        Q ∈ section7HStarFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes)} =>
      (R : Subgroup G)) hEq

/-- In branch (b), maximality makes every `H_G^*(F(M);q)` member normalized by `M`. -/
public theorem CFSG.section8_HStarFamily_fitting_le_normalizer_maximal_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩)
    {Q : Subgroup G}
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
      ({q} : Set Nat.Primes)) :
    M ≤ Subgroup.normalizer (Q : Set G) := by
  have hMnormF : M ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
    have hFNorm : ((section8FittingSubgroup M).subgroupOf M).Normal :=
      section8FittingSubgroup_normal_in M
    let : ((section8FittingSubgroup M).subgroupOf M).Normal := hFNorm
    exact Subgroup.le_normalizer_of_normal_subgroupOf (section8FittingSubgroup_le M)
  have hsubF :
      Subsingleton {R : Subgroup G //
        R ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
          ({q} : Set Nat.Primes)} :=
    section8_HStarFamily_fitting_subsingleton_of_fitting_isPGroup hM hpF hFp P hA hq
  intro m hm
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hx
  have hQconj : Q.conjBy m ∈
      section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
        ({q} : Set Nat.Primes) :=
    section8_mem_section7HStarFamily_top_conjBy_of_mem_normalizer (hMnormF hm) hQ
  have hQconj_eq : Q.conjBy m = Q := by
    have hEq :=
      Subsingleton.elim
        (⟨Q.conjBy m, hQconj⟩ :
          {R : Subgroup G //
            R ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
              ({q} : Set Nat.Primes)})
        (⟨Q, hQ⟩ :
          {R : Subgroup G //
            R ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
              ({q} : Set Nat.Primes)})
    exact congrArg Subtype.val hEq
  have hx_conj : m * x * m⁻¹ ∈ Q.conjBy m :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  simpa [hQconj_eq] using hx_conj

/-- In branch (b), every member of `H_G^*(F(M);q)` is trivial for `q ≠ p`. -/
public theorem CFSG.section8_HStarFamily_fitting_eq_bot_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩)
    {Q : Subgroup G}
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) (section8FittingSubgroup M)
      ({q} : Set Nat.Primes)) :
    Q = ⊥ := by
  by_contra hQ_ne_bot
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
    hQ.1.2.1
  have hQ_ne_top : Q ≠ ⊤ :=
    section8_ne_top_of_isPiSubgroup_singleton_ne_bot hQπ hQ_ne_bot
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    section8_HStarFamily_fitting_le_normalizer_maximal_of_fitting_isPGroup
      hM hpF hFp P hA hq hQ
  have hnorm_ne_top : Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
    intro hnorm_top
    have hQnorm : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
    let : IsSimpleGroup G := IsMinCE.simple
    rcases (haveI := hQnorm; IsSimpleGroup.eq_bot_or_eq_top_of_normal Q) with hQbot | hQtop
    · exact hQ_ne_bot hQbot
    · exact hQ_ne_top hQtop
  have hnorm_eq : Subgroup.normalizer (Q : Set G) = M :=
    section8MaximalSubgroups_eq_of_le hM hMnormQ hnorm_ne_top
  have hQM : Q ≤ M := by
    simpa [hnorm_eq] using (Subgroup.le_normalizer : Q ≤ Subgroup.normalizer (Q : Set G))
  have hQnormM : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
  have hQcop : Nat.Coprime p (Nat.card (Q.subgroupOf M)) := by
    have hp_not_dvd_Q : ¬ p ∣ Nat.card Q := by
      intro hpQ
      have hp_mem : (⟨p, Fact.out⟩ : Nat.Primes) ∈ ({q} : Set Nat.Primes) :=
        hQπ ⟨p, Fact.out⟩ hpQ
      have hp_eq_q : (⟨p, Fact.out⟩ : Nat.Primes) = q := by
        exact hp_mem
      exact hq hp_eq_q.symm
    have hcard : Nat.card (Q.subgroupOf M) = Nat.card Q :=
      natCard_subgroupOf_eq _ _ hQM
    have hp_not_dvd_Qsub : ¬ p ∣ Nat.card (Q.subgroupOf M) := by
      intro hpQsub
      exact hp_not_dvd_Q (by simpa [hcard] using hpQsub)
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hp_not_dvd_Qsub
  have hcore : pPrimeCore p M = ⊥ :=
    section8_pPrimeCore_eq_bot_of_fitting_isPGroup hM hFp
  have hQsub_le_core : Q.subgroupOf M ≤ pPrimeCore p M :=
    le_sSup ⟨hQnormM, hQcop⟩
  have hQsub_bot : Q.subgroupOf M = ⊥ :=
    le_bot_iff.mp (by simpa [hcore] using hQsub_le_core)
  have hQbot : Q = ⊥ := by
    calc
      Q = (Q.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hQM).symm
      _ = ⊥ := by simp [hQsub_bot]
  exact hQ_ne_bot hQbot

/-- In branch (b), every member of `H_G^*(A;q)` is trivial for transported
`A ∈ SCN_3(P)` and `q ≠ p`. -/
public theorem CFSG.section8_HStarFamily_sylowSubgroupInAmbient_eq_bot_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩)
    {Q : Subgroup G}
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G)
      (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes)) :
    Q = ⊥ := by
  let F : Subgroup G := section8FittingSubgroup M
  have hbotF : (⊥ : Subgroup G) ∈
      section7HFamily (⊤ : Subgroup G) F ({q} : Set Nat.Primes) :=
    section8_bot_mem_section7HFamily_top F ({q} : Set Nat.Primes)
  rcases section8_exists_mem_section7HStarFamily_of_mem_family hbotF with
    ⟨QF, hQFstar, _hbot_le_QF⟩
  have hsubset :
      section7HStarFamily (⊤ : Subgroup G) F ({q} : Set Nat.Primes) ⊆
        section7HStarFamily (⊤ : Subgroup G)
          (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes) := by
    simpa [F] using
      section8_HStarFamily_fitting_subset_sylowSubgroupInAmbient_of_fitting_isPGroup
        hM hpF hFp P hA hq
  have hsubA :
      Subsingleton {R : Subgroup G //
        R ∈ section7HStarFamily (⊤ : Subgroup G)
          (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes)} :=
    section8_HStarFamily_sylowSubgroupInAmbient_subsingleton_of_fitting_isPGroup
      hM hpF hFp P hA hq
  have hQ_eq_QF : Q = QF := by
    have hEq :=
      Subsingleton.elim
        (⟨Q, hQ⟩ :
          {R : Subgroup G //
            R ∈ section7HStarFamily (⊤ : Subgroup G)
              (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes)})
        (⟨QF, hsubset hQFstar⟩ :
          {R : Subgroup G //
            R ∈ section7HStarFamily (⊤ : Subgroup G)
              (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes)})
    exact congrArg Subtype.val hEq
  have hQF_bot : QF = ⊥ :=
    section8_HStarFamily_fitting_eq_bot_of_fitting_isPGroup
      hM hpF hFp P hA hq hQFstar
  exact hQ_eq_QF.trans hQF_bot

/-- In branch (b), `H_G(A;q)` is exactly `{⊥}` for transported `A ∈ SCN_3(P)` and
`q ≠ p`. -/
public theorem CFSG.section8_HFamily_sylowSubgroupInAmbient_eq_singleton_bot_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩) :
    section7HFamily (⊤ : Subgroup G)
      (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes) =
        ({⊥} : Set (Subgroup G)) := by
  ext R
  constructor
  · intro hR
    rcases section8_exists_mem_section7HStarFamily_of_mem_family hR with
      ⟨Q, hQstar, hRQ⟩
    have hQbot : Q = ⊥ :=
      section8_HStarFamily_sylowSubgroupInAmbient_eq_bot_of_fitting_isPGroup
        hM hpF hFp P hA hq hQstar
    have hRbot : R = ⊥ :=
      le_bot_iff.mp (by simpa [hQbot] using hRQ)
    simp [hRbot]
  · intro hR
    have hRbot : R = ⊥ := by simpa using hR
    rw [hRbot]
    exact section8_bot_mem_section7HFamily_top
      (section8SylowSubgroupInAmbient M P A) ({q} : Set Nat.Primes)

/-- In branch (b), `H_G(A;p')` is exactly `{⊥}` for transported
`A ∈ SCN_3(P)`. -/
public theorem CFSG.section8_HFamily_sylowSubgroupInAmbient_pPrime_eq_singleton_bot_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M)) :
    section7HFamily (⊤ : Subgroup G)
      (section8SylowSubgroupInAmbient M P A)
      (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) =
        ({⊥} : Set (Subgroup G)) := by
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  ext Y
  constructor
  · intro hY
    have hp_dvd_G : p ∣ Nat.card G :=
      (hpF : p ∣ Nat.card (section8FittingSubgroup M)).trans
        (Subgroup.card_subgroup_dvd_card (section8FittingSubgroup M))
    have hp_not_dvd_Y : ¬ p ∣ Nat.card Y := by
      intro hpY
      have hp_mem : (⟨p, Fact.out⟩ : Nat.Primes) ∈
          (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) :=
        hY.2.1 ⟨p, Fact.out⟩ hpY
      exact hp_mem (Set.mem_singleton _)
    have hY_ne_top : Y ≠ ⊤ := by
      intro hYtop
      have hpY : p ∣ Nat.card Y := by
        simpa [hYtop] using hp_dvd_G
      exact hp_not_dvd_Y hpY
    have : Group.IsSolvable Y :=
      IsMinCE.proper_subgroups_solvable Y (lt_top_iff_ne_top.mpr hY_ne_top)
    have hpCore_bot :
        ∀ r : (Nat.card Y).primeFactors.attach, pCore r.1.1 Y = ⊥ := by
      intro r
      let q : Nat.Primes := ⟨r.1.1, Nat.prime_of_mem_primeFactors r.1.2⟩
      have : Fact q.val.Prime := ⟨q.2⟩
      have hq_dvd_Y : q.val ∣ Nat.card Y := by
        exact Nat.dvd_of_mem_primeFactors r.1.2
      have hq_mem_compl : q ∈ (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) :=
        hY.2.1 q hq_dvd_Y
      have hq_ne_p : q ≠ ⟨p, Fact.out⟩ := by
        intro hqp
        exact hq_mem_compl (Set.mem_singleton_iff.mpr hqp)
      have hpi_mem : piCoreIn ({q} : Set Nat.Primes) Y ∈
          section7HFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes) := by
        simpa [A_G] using
          section8_piCoreIn_singleton_mem_section7HFamily_top_of_mem_family
            (q := q) hY
      have hfamily_eq :
          section7HFamily (⊤ : Subgroup G) A_G ({q} : Set Nat.Primes) =
            ({⊥} : Set (Subgroup G)) := by
        simpa [A_G] using
          section8_HFamily_sylowSubgroupInAmbient_eq_singleton_bot_of_fitting_isPGroup
            hM hpF hFp P hA hq_ne_p
      have hpi_bot : piCoreIn ({q} : Set Nat.Primes) Y = ⊥ := by
        have hmem_single : piCoreIn ({q} : Set Nat.Primes) Y ∈
            ({⊥} : Set (Subgroup G)) := by
          simpa [hfamily_eq] using hpi_mem
        simpa using hmem_single
      have hpCore_map_bot : (pCore q.val Y).map Y.subtype = ⊥ := by
        simpa [section8_piCoreIn_singleton_eq_pCore_map q Y] using hpi_bot
      have hpCore_map_bot' :
          (pCore q.val Y).map Y.subtype = (⊥ : Subgroup Y).map Y.subtype := by
        simpa using hpCore_map_bot
      have hpCore_bot_q : pCore q.val Y = ⊥ :=
        Subgroup.map_injective Y.subtype_injective hpCore_map_bot'
      simpa [q] using hpCore_bot_q
    have hsup_bot :
        (⨆ r : (Nat.card Y).primeFactors.attach, pCore r.1.1 Y) = ⊥ := by
      apply le_bot_iff.mp
      refine iSup_le ?_
      intro r
      simp [hpCore_bot r]
    have hfit_le_sup :
        fittingSubgroup Y ≤
          ⨆ r : (Nat.card Y).primeFactors.attach, pCore r.1.1 Y :=
      normal_nilpotent_le_sup_pCore
        (G := Y) (N := fittingSubgroup Y)
        (inferInstance : (fittingSubgroup Y).Normal)
        (by infer_instance)
    have hfit_bot : fittingSubgroup Y = ⊥ :=
      le_bot_iff.mp (by simpa [hsup_bot] using hfit_le_sup)
    have hcardY : Nat.card Y = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable Y).mp hfit_bot
    have hYbot : Y = ⊥ :=
      (Subgroup.card_eq_one (H := Y)).1 hcardY
    simp [hYbot]
  · intro hY
    have hYbot : Y = ⊥ := by simpa using hY
    rw [hYbot]
    exact section8_bot_mem_section7HFamily_top
      (section8SylowSubgroupInAmbient M P A)
      (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ)

/-- In branch (b), the `p'`-core of any maximal overgroup of a transported
`SCN_3(P)` subgroup is trivial. -/
public theorem CFSG.section8_pPrimeCore_maximalOver_sylowSubgroupInAmbient_eq_bot_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A)) :
    pPrimeCore p N = ⊥ := by
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  let πp : Set Nat.Primes := ({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ
  have hAN : A_G ≤ N := by
    simpa [A_G] using hN.2
  have hA_norm_N : A_G ≤ Subgroup.normalizer (N : Set G) :=
    hAN.trans Subgroup.le_normalizer
  have hpi_mem : piCoreIn πp N ∈ section7HFamily (⊤ : Subgroup G) A_G πp := by
    refine ⟨le_top, piCoreIn_isPiSubgroup (G := G) πp N, ?_⟩
    exact section8_le_normalizer_piCoreIn_of_le_normalizer hA_norm_N
  have hfamily_eq :
      section7HFamily (⊤ : Subgroup G) A_G πp = ({⊥} : Set (Subgroup G)) := by
    simpa [A_G, πp] using
      section8_HFamily_sylowSubgroupInAmbient_pPrime_eq_singleton_bot_of_fitting_isPGroup
        hM hpF hFp P hA
  have hpi_bot : piCoreIn πp N = (⊥ : Subgroup G) := by
    have hmem_single : piCoreIn πp N ∈ ({⊥} : Set (Subgroup G)) := by
      simpa [hfamily_eq] using hpi_mem
    simpa using hmem_single
  have hmap_bot : (pPrimeCore p N).map N.subtype = (⊥ : Subgroup G) := by
    simpa [πp, section8_piCoreIn_singleton_compl_eq_pPrimeCore_map] using hpi_bot
  have hmap_bot' :
      (pPrimeCore p N).map N.subtype = (⊥ : Subgroup N).map N.subtype := by
    simpa using hmap_bot
  exact Subgroup.map_injective N.subtype_injective hmap_bot'

/-- A maximal overgroup of a transported `SCN_3(P)` subgroup has order divisible by `p`. -/
public theorem CFSG.section8_prime_dvd_card_maximalOver_sylowSubgroupInAmbient
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A)) :
    p ∣ Nat.card N := by
  have hp_dvd_G : p ∣ Nat.card G :=
    (hpF : p ∣ Nat.card (section8FittingSubgroup M)).trans
      (Subgroup.card_subgroup_dvd_card (section8FittingSubgroup M))
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hAπ :
      subgroupPrimeSet (section8SylowSubgroupInAmbient M P A) =
        ({⟨p, Fact.out⟩} : Set Nat.Primes) :=
    section8_subgroupPrimeSet_sylowSubgroupInAmbient_eq_singleton hpodd P hA
  have hpA : p ∣ Nat.card (section8SylowSubgroupInAmbient M P A) := by
    have hpA' : (⟨p, Fact.out⟩ : Nat.Primes) ∈
        subgroupPrimeSet (section8SylowSubgroupInAmbient M P A) := by
      rw [hAπ]
      exact Set.mem_singleton _
    exact hpA'
  exact hpA.trans (Subgroup.card_dvd_of_le hN.2)

/-- In branch (b), Theorem 6.2 makes `Z(J(R))` normal in any maximal overgroup
of the transported `SCN_3(P)` subgroup. -/
public theorem CFSG.section8_centerIn_thompsonSubgroup_normal_of_maximalOver_sylowSubgroupInAmbient
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A))
    (R : Sylow p N) :
    (centerIn (thompsonSubgroup R) : Subgroup N).Normal := by
  have : Group.IsSolvable N :=
    IsMinCE.proper_subgroups_solvable N (lt_top_iff_ne_top.mpr hN.1.1)
  have hNodd : Odd (Nat.card N) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card N)
  have hcore : pPrimeCore p N = ⊥ :=
    section8_pPrimeCore_maximalOver_sylowSubgroupInAmbient_eq_bot_of_fitting_isPGroup
      hM hpF hFp P hA hN
  have hnorm : (centerIn (thompsonSubgroup R) ⊔ pPrimeCore p N : Subgroup N).Normal :=
    theorem_6_2 (G := N) hNodd R
  simpa [hcore] using hnorm

/-- In branch (b), the ambient normalizer of `Z(J(R))` is the maximal overgroup
in which `R` is Sylow. -/
public theorem CFSG.section8_normalizer_centerIn_thompsonSubgroup_eq_of_maximalOver_sylowSubgroupInAmbient
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A))
    (R : Sylow p N) :
    Subgroup.normalizer
        (section8SubgroupInAmbient (centerIn (thompsonSubgroup R) : Subgroup N) : Set G) = N := by
  have hpN : p ∣ Nat.card N :=
    section8_prime_dvd_card_maximalOver_sylowSubgroupInAmbient hpF P hA hN
  have hR_ne_bot : (R : Subgroup N) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := N) (p := p) R hpN
  have hZJ_ne_bot : (centerIn (thompsonSubgroup R) : Subgroup N) ≠ ⊥ :=
    section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot R.isPGroup' hR_ne_bot
  have hZJ_norm : (centerIn (thompsonSubgroup R) : Subgroup N).Normal :=
    section8_centerIn_thompsonSubgroup_normal_of_maximalOver_sylowSubgroupInAmbient
      hM hpF hFp P hA hN R
  exact
    section8_normalizer_subgroupInAmbient_eq_of_nontrivial_normal_in_maximal
      hN.1 hZJ_ne_bot hZJ_norm

/-- In branch (b), every Sylow `p`-subgroup of a maximal overgroup of the transported
`SCN_3(P)` subgroup is also Sylow in the ambient group. -/
public theorem CFSG.section8_sylowOf_maximalOver_sylowSubgroupInAmbient_is_sylow_global
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A))
    (R : Sylow p N) :
    ∃ R₀ : Sylow p G,
      (R₀ : Subgroup G) = section8SubgroupInAmbient (R : Subgroup N) := by
  have hZJnorm :
      Subgroup.normalizer
          (section8SubgroupInAmbient (centerIn (thompsonSubgroup R) : Subgroup N) : Set G) = N :=
    section8_normalizer_centerIn_thompsonSubgroup_eq_of_maximalOver_sylowSubgroupInAmbient
      hM hpF hFp P hA hN R
  refine section8SubgroupInAmbient_sylow_of_normalizer_le R ?_
  simpa [hZJnorm] using
    section8_normalizer_centerIn_thompsonSubgroup_le_of_normalizer_sylow R


/-- If there is a counterexample maximal overgroup in branch (b), choose one maximizing
the `p`-part of its intersection with `M`. -/
public theorem CFSG.section8_exists_maximal_counterexample_inf_factorization
    [Finite G] {p : ℕ} {M A_G : Subgroup G}
    (hne : ∃ N : Subgroup G, N ∈ section8MaximalSubgroupsContaining A_G ∧ N ≠ M) :
    ∃ H : Subgroup G,
      H ∈ section8MaximalSubgroupsContaining A_G ∧ H ≠ M ∧
        ∀ K : Subgroup G, K ∈ section8MaximalSubgroupsContaining A_G → K ≠ M →
          Nat.factorization (Nat.card (K ⊓ M : Subgroup G)) p ≤
            Nat.factorization (Nat.card (H ⊓ M : Subgroup G)) p := by
  let C : Set (Subgroup G) := {N | N ∈ section8MaximalSubgroupsContaining A_G ∧ N ≠ M}
  have hCfinite : C.Finite := Set.toFinite C
  have hImageFinite :
      ((fun N : Subgroup G => Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p) ''
        C).Finite :=
    hCfinite.image _
  have hCnonempty : C.Nonempty := by
    rcases hne with ⟨N, hN, hNM⟩
    exact ⟨N, hN, hNM⟩
  obtain ⟨H, hHmax⟩ :=
    hImageFinite.exists_maximalFor'
      (f := fun N : Subgroup G => Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p)
      C hCnonempty
  refine ⟨H, hHmax.1.1, hHmax.1.2, ?_⟩
  intro K hK hKM
  exact hHmax.le ⟨hK, hKM⟩

/-- A maximal overgroup of a transported `SCN_3(P)` subgroup has a Sylow subgroup of
`N ∩ M` whose ambient image contains that transported subgroup. -/
public theorem CFSG.section8_exists_sylow_inf_maximalOver_containing_sylowSubgroupInAmbient
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A)) :
    ∃ R : Sylow p (N ⊓ M : Subgroup G),
      section8SylowSubgroupInAmbient M P A ≤
        section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) := by
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  have hAinf : A_G ≤ (N ⊓ M : Subgroup G) := by
    intro x hx
    exact ⟨hN.2 hx, section8SylowSubgroupInAmbient_le M P A hx⟩
  have hA_G_p : IsPGroup p A_G := by
    simpa [A_G] using section8SylowSubgroupInAmbient_isPGroup M P A
  have hA_inf_p : IsPGroup p (A_G.subgroupOf (N ⊓ M : Subgroup G)) :=
    hA_G_p.of_equiv (Subgroup.subgroupOfEquivOfLe hAinf).symm
  rcases IsPGroup.exists_le_sylow hA_inf_p with ⟨R, hA_le_R⟩
  refine ⟨R, ?_⟩
  intro x hxA
  have hxInf : x ∈ (N ⊓ M : Subgroup G) := hAinf hxA
  let xInf : (N ⊓ M : Subgroup G) := ⟨x, hxInf⟩
  have hxA_inf : xInf ∈ A_G.subgroupOf (N ⊓ M : Subgroup G) := by
    change x ∈ A_G
    exact hxA
  exact Subgroup.mem_map_of_mem (N ⊓ M : Subgroup G).subtype (hA_le_R hxA_inf)


/-- If a maximal overgroup and `M` share the same ambient Sylow `p`-subgroup, then they
are equal. -/
public theorem CFSG.section8_eq_maximalOver_sylowSubgroupInAmbient_of_common_sylow
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A))
    (R_N : Sylow p N) (R_M : Sylow p M)
    (hR :
      section8SubgroupInAmbient (R_N : Subgroup N) =
        section8SubgroupInAmbient (R_M : Subgroup M)) :
    N = M := by
  have hnormN_R :
      Subgroup.normalizer
          (section8SubgroupInAmbient (centerIn (thompsonSubgroup R_N) : Subgroup N) :
            Set G) = N :=
    section8_normalizer_centerIn_thompsonSubgroup_eq_of_maximalOver_sylowSubgroupInAmbient
      hM hpF hFp P hA hN R_N
  have hZR :
      section8SubgroupInAmbient (centerIn (thompsonSubgroup R_M) : Subgroup M) =
        section8SubgroupInAmbient (centerIn (thompsonSubgroup R_N) : Subgroup N) :=
    section8_centerIn_thompsonSubgroup_eq_of_sylow_ambient_eq R_M R_N hR.symm
  have hnormN_MR :
      Subgroup.normalizer
          (section8SubgroupInAmbient (centerIn (thompsonSubgroup R_M) : Subgroup M) :
            Set G) = N := by
    rw [hZR]
    exact hnormN_R
  have hnormM_R :
      Subgroup.normalizer
          (section8SubgroupInAmbient (centerIn (thompsonSubgroup R_M) : Subgroup M) :
            Set G) = M :=
    section8_normalizer_centerIn_thompsonSubgroup_eq_of_fitting_isPGroup hM hpF hFp R_M
  exact hnormN_MR.symm.trans hnormM_R

/-- If a Sylow subgroup chosen in `N ∩ M` is also the ambient image of a Sylow subgroup
of `N`, then the maximal overgroup `N` is equal to `M`. -/
public theorem CFSG.section8_eq_maximalOver_sylowSubgroupInAmbient_of_inf_sylow_is_sylow
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A))
    (R : Sylow p (N ⊓ M : Subgroup G)) (R_N : Sylow p N)
    (hR_N :
      section8SubgroupInAmbient (R_N : Subgroup N) =
        section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G))) :
    N = M := by
  rcases section8_sylowOf_maximalOver_sylowSubgroupInAmbient_is_sylow_global
      hM hpF hFp P hA hN R_N with
    ⟨R₀, hR₀eq⟩
  have hR₀M : (R₀ : Subgroup G) ≤ M := by
    intro x hxR₀
    have hxR_N : x ∈ section8SubgroupInAmbient (R_N : Subgroup N) := by
      simpa [hR₀eq] using hxR₀
    have hxR : x ∈ section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) := by
      simpa [hR_N] using hxR_N
    exact (inf_le_right : (N ⊓ M : Subgroup G) ≤ M) (section8SubgroupInAmbient_le _ hxR)
  rcases section8_sylow_subgroupOf_of_global_sylow_le R₀ hR₀M with ⟨R_M, hR_M⟩
  refine
    section8_eq_maximalOver_sylowSubgroupInAmbient_of_common_sylow
      hM hpF hFp P hA hN R_N R_M ?_
  calc
    section8SubgroupInAmbient (R_N : Subgroup N) = (R₀ : Subgroup G) := hR₀eq.symm
    _ = section8SubgroupInAmbient (R_M : Subgroup M) := by
      simpa [section8SubgroupInAmbient] using hR_M.symm

/-- If the ambient normalizer of a Sylow subgroup of `N ∩ M` is contained in `M`,
then the same ambient subgroup is the image of a Sylow subgroup of `N`. -/
public theorem CFSG.section8_exists_sylow_left_eq_inf_sylow_of_normalizer_le
    [Finite G] {p : ℕ} [Fact p.Prime] {M N : Subgroup G}
    (R : Sylow p (N ⊓ M : Subgroup G))
    (hnorm : Subgroup.normalizer
        (section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) : Set G) ≤ M) :
    ∃ R_N : Sylow p N,
      section8SubgroupInAmbient (R_N : Subgroup N) =
        section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) := by
  let K : Subgroup N := (N ⊓ M : Subgroup G).subgroupOf N
  let e : (N ⊓ M : Subgroup G) ≃* K :=
    (Subgroup.subgroupOfEquivOfLe (H := (N ⊓ M : Subgroup G)) (K := N)
      inf_le_left).symm
  let R_K_sub : Subgroup K := (R : Subgroup (N ⊓ M : Subgroup G)).map e.toMonoidHom
  have he_inj : Function.Injective e.toMonoidHom := e.injective
  have hcard_R_K : Nat.card R_K_sub = p ^ Nat.factorization (Nat.card K) p := by
    have hcard_map : Nat.card R_K_sub = Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) := by
      simpa [R_K_sub] using
        Subgroup.card_map_of_injective (K := (R : Subgroup (N ⊓ M : Subgroup G)))
          (f := e.toMonoidHom) he_inj
    have hcard_K : Nat.card K = Nat.card (N ⊓ M : Subgroup G) := by
      exact Nat.card_congr e.symm.toEquiv
    rw [hcard_map, Sylow.card_eq_multiplicity R, hcard_K]
  let R_K : Sylow p K := Sylow.ofCard R_K_sub hcard_R_K
  have hRK_image :
      (section8SubgroupInAmbient (G := N) (R_K : Subgroup K)).map N.subtype =
        section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨xN, hxN_RK, rfl⟩
      change (xN : G) ∈ section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G))
      change xN ∈ R_K_sub.map K.subtype at hxN_RK
      rcases Subgroup.mem_map.mp hxN_RK with ⟨xK, hxK_R, hxK_eq⟩
      rcases Subgroup.mem_map.mp hxK_R with ⟨xR, hxR, hxR_eq⟩
      exact Subgroup.mem_map.mpr ⟨xR, hxR, by
        have hxKN : (xK : N) = xN := hxK_eq
        have hxG : (xR : G) = (xN : G) := by
          calc
            (xR : G) = (((e xR : K) : N) : G) := by rfl
            _ = (xK : G) := congrArg (fun z : K => ((z : N) : G)) hxR_eq
            _ = (xN : G) := congrArg Subtype.val hxKN
        exact hxG⟩
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨xR, hxR, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨((e xR : K) : N), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨(e xR : K), by
          change (e xR : K) ∈ R_K_sub
          exact Subgroup.mem_map_of_mem e.toMonoidHom hxR, rfl⟩
      · rfl
  have hnormN :
      Subgroup.normalizer (section8SubgroupInAmbient (G := N) (R_K : Subgroup K) : Set N) ≤
        K := by
    intro n hn
    have hnG_norm : (n : G) ∈ Subgroup.normalizer
        (section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) : Set G) := by
      refine Subgroup.mem_normalizer_fintype ?_
      intro x hxR
      have hxN : x ∈ N :=
        (inf_le_left : (N ⊓ M : Subgroup G) ≤ N) (section8SubgroupInAmbient_le _ hxR)
      let xN : N := ⟨x, hxN⟩
      have hxN_RK : xN ∈ section8SubgroupInAmbient (G := N) (R_K : Subgroup K) := by
        have hx_map :
            x ∈ (section8SubgroupInAmbient (G := N) (R_K : Subgroup K)).map N.subtype := by
          simpa [hRK_image] using hxR
        rcases Subgroup.mem_map.mp hx_map with ⟨y, hy, hyx⟩
        have hy_eq : y = xN := Subtype.ext hyx
        simpa [← hy_eq] using hy
      have hconjN : n * xN * n⁻¹ ∈ section8SubgroupInAmbient (G := N) (R_K : Subgroup K) :=
        (Subgroup.mem_normalizer_iff.mp hn xN).1 hxN_RK
      have hconj_map : ((n * xN * n⁻¹ : N) : G) ∈
          (section8SubgroupInAmbient (G := N) (R_K : Subgroup K)).map N.subtype :=
        Subgroup.mem_map_of_mem N.subtype hconjN
      simpa [hRK_image, xN, mul_assoc] using hconj_map
    exact ⟨n.property, hnorm hnG_norm⟩
  rcases section8SubgroupInAmbient_sylow_of_normalizer_le (G := N) (M := K) R_K hnormN with
    ⟨R_N, hR_N⟩
  refine ⟨R_N, ?_⟩
  calc
    section8SubgroupInAmbient (R_N : Subgroup N) =
        ((R_N : Subgroup N).map N.subtype) := rfl
    _ = (section8SubgroupInAmbient (G := N) (R_K : Subgroup K)).map N.subtype := by
      rw [hR_N]
    _ = section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) := hRK_image

/-- In branch (b), normalizer control for a Sylow subgroup of `N ∩ M` forces the
maximal overgroup `N` to be `M`. -/
public theorem CFSG.section8_eq_maximalOver_sylowSubgroupInAmbient_of_inf_sylow_normalizer_le
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A))
    (R : Sylow p (N ⊓ M : Subgroup G))
    (hnorm : Subgroup.normalizer
        (section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) : Set G) ≤ M) :
    N = M := by
  rcases section8_exists_sylow_left_eq_inf_sylow_of_normalizer_le R hnorm with
    ⟨R_N, hR_N⟩
  exact
    section8_eq_maximalOver_sylowSubgroupInAmbient_of_inf_sylow_is_sylow
      hM hpF hFp P hA hN R R_N hR_N


/-- If a Sylow subgroup of `N ∩ M` has the same order as a Sylow subgroup of `M`,
then its ambient image is also the image of a Sylow subgroup of `M`. -/
public theorem CFSG.section8_exists_sylow_right_eq_inf_sylow_of_card_eq
    [Finite G] {p : ℕ} [Fact p.Prime] {M N : Subgroup G}
    (P : Sylow p M) (R : Sylow p (N ⊓ M : Subgroup G))
    (hcard : Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) = Nat.card (P : Subgroup M)) :
    ∃ R_M : Sylow p M,
      section8SubgroupInAmbient (R_M : Subgroup M) =
        section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) := by
  let K : Subgroup M := (N ⊓ M : Subgroup G).subgroupOf M
  let e : (N ⊓ M : Subgroup G) ≃* K :=
    (Subgroup.subgroupOfEquivOfLe (H := (N ⊓ M : Subgroup G)) (K := M)
      inf_le_right).symm
  let R_K_sub : Subgroup K := (R : Subgroup (N ⊓ M : Subgroup G)).map e.toMonoidHom
  let R_M_sub : Subgroup M := R_K_sub.map K.subtype
  have he_inj : Function.Injective e.toMonoidHom := e.injective
  have hcard_R_K : Nat.card R_K_sub = Nat.card (P : Subgroup M) := by
    have hcard_map : Nat.card R_K_sub = Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) := by
      simpa [R_K_sub] using
        Subgroup.card_map_of_injective (K := (R : Subgroup (N ⊓ M : Subgroup G)))
          (f := e.toMonoidHom) he_inj
    rw [hcard_map, hcard]
  have hcard_R_M : Nat.card R_M_sub = p ^ Nat.factorization (Nat.card M) p := by
    have hcard_map : Nat.card R_M_sub = Nat.card R_K_sub := by
      simpa [R_M_sub] using
        Subgroup.card_map_of_injective (K := R_K_sub) (f := K.subtype) K.subtype_injective
    rw [hcard_map, hcard_R_K, Sylow.card_eq_multiplicity P]
  let R_M : Sylow p M := Sylow.ofCard R_M_sub hcard_R_M
  refine ⟨R_M, ?_⟩
  ext x
  constructor
  · intro hx
    change x ∈ (R_M : Subgroup M).map M.subtype at hx
    change x ∈ R_M_sub.map M.subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxM_RM, rfl⟩
    change xM ∈ R_M_sub at hxM_RM
    rcases Subgroup.mem_map.mp hxM_RM with ⟨xK, hxK_RK, hxK_eq⟩
    rcases Subgroup.mem_map.mp hxK_RK with ⟨xR, hxR, hxR_eq⟩
    exact Subgroup.mem_map.mpr ⟨xR, hxR, by
      have hxKM : (xK : M) = xM := hxK_eq
      calc
        (xR : G) = (((e xR : K) : M) : G) := by rfl
        _ = (xK : G) := congrArg (fun z : K => ((z : M) : G)) hxR_eq
        _ = (xM : G) := congrArg Subtype.val hxKM⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨xR, hxR, rfl⟩
    change ((xR : (N ⊓ M : Subgroup G)) : G) ∈ (R_M : Subgroup M).map M.subtype
    change ((xR : (N ⊓ M : Subgroup G)) : G) ∈ R_M_sub.map M.subtype
    refine Subgroup.mem_map.mpr ?_
    refine ⟨((e xR : K) : M), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem K.subtype (Subgroup.mem_map_of_mem e.toMonoidHom hxR)
    · rfl

/-- A Sylow subgroup of `N ∩ M`, viewed as a `p`-subgroup of `M`, has order at most
that of a Sylow subgroup of `M`. -/
public theorem CFSG.section8_inf_sylow_card_le_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] {M N : Subgroup G}
    (P : Sylow p M) (R : Sylow p (N ⊓ M : Subgroup G)) :
    Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) ≤ Nat.card (P : Subgroup M) := by
  let K : Subgroup M := (N ⊓ M : Subgroup G).subgroupOf M
  let e : (N ⊓ M : Subgroup G) ≃* K :=
    (Subgroup.subgroupOfEquivOfLe (H := (N ⊓ M : Subgroup G)) (K := M)
      inf_le_right).symm
  let R_K_sub : Subgroup K := (R : Subgroup (N ⊓ M : Subgroup G)).map e.toMonoidHom
  let R_M_sub : Subgroup M := R_K_sub.map K.subtype
  have hcard_R_K : Nat.card R_K_sub = Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) := by
    simpa [R_K_sub] using
      Subgroup.card_map_of_injective (K := (R : Subgroup (N ⊓ M : Subgroup G)))
        (f := e.toMonoidHom) e.injective
  have hcard_R_M : Nat.card R_M_sub = Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) := by
    have hcard_map : Nat.card R_M_sub = Nat.card R_K_sub := by
      simpa [R_M_sub] using
        Subgroup.card_map_of_injective (K := R_K_sub) (f := K.subtype) K.subtype_injective
    rw [hcard_map, hcard_R_K]
  have hR_K_p : IsPGroup p R_K_sub := IsPGroup.map R.isPGroup' e.toMonoidHom
  have hR_M_p : IsPGroup p R_M_sub := IsPGroup.map hR_K_p K.subtype
  rcases IsPGroup.exists_le_sylow hR_M_p with ⟨P', hR_le_P'⟩
  have hcard_R_le_P' : Nat.card R_M_sub ≤ Nat.card (P' : Subgroup M) :=
    Subgroup.card_le_of_le hR_le_P'
  have hP'_card_eq_P : Nat.card (P' : Subgroup M) = Nat.card (P : Subgroup M) := by
    rw [Sylow.card_eq_multiplicity P', Sylow.card_eq_multiplicity P]
  calc
    Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) = Nat.card R_M_sub := hcard_R_M.symm
    _ ≤ Nat.card (P' : Subgroup M) := hcard_R_le_P'
    _ = Nat.card (P : Subgroup M) := hP'_card_eq_P

/-- In the equal-order case of branch (b), the normalizer of the Sylow subgroup chosen in
`N ∩ M` lies in `M`. -/
public theorem CFSG.section8_inf_sylow_normalizer_le_of_card_eq_sylowSubgroupInAmbient
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M N : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) (R : Sylow p (N ⊓ M : Subgroup G))
    (hcard : Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) = Nat.card (P : Subgroup M)) :
    Subgroup.normalizer
        (section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) : Set G) ≤ M := by
  rcases section8_exists_sylow_right_eq_inf_sylow_of_card_eq P R hcard with
    ⟨R_M, hR_M⟩
  have hnormZ :
      Subgroup.normalizer
          (section8SubgroupInAmbient (centerIn (thompsonSubgroup R_M) : Subgroup M) :
            Set G) = M :=
    section8_normalizer_centerIn_thompsonSubgroup_eq_of_fitting_isPGroup hM hpF hFp R_M
  have hnormR :
      Subgroup.normalizer (section8SubgroupInAmbient (R_M : Subgroup M) : Set G) ≤ M := by
    simpa [hnormZ] using
      section8_normalizer_centerIn_thompsonSubgroup_le_of_normalizer_sylow R_M
  rw [← hR_M]
  exact hnormR

/-- If the Sylow subgroup chosen in `N ∩ M` has smaller order than a Sylow subgroup of
`M`, then its ambient normalizer has larger `p`-part after intersecting `M`. -/
public theorem CFSG.section8_inf_sylow_normalizer_factorization_gt_of_card_lt
    [Finite G] {p : ℕ} [Fact p.Prime] {M N : Subgroup G}
    (P : Sylow p M) (R : Sylow p (N ⊓ M : Subgroup G))
    (hcard_lt :
      Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) < Nat.card (P : Subgroup M)) :
    Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p <
      Nat.factorization
        (Nat.card
          (Subgroup.normalizer
            (section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) : Set G) ⊓
              M : Subgroup G)) p := by
  let R_G : Subgroup G := section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G))
  let K : Subgroup M := (N ⊓ M : Subgroup G).subgroupOf M
  let e : (N ⊓ M : Subgroup G) ≃* K :=
    (Subgroup.subgroupOfEquivOfLe (H := (N ⊓ M : Subgroup G)) (K := M)
      inf_le_right).symm
  let R_K_sub : Subgroup K := (R : Subgroup (N ⊓ M : Subgroup G)).map e.toMonoidHom
  let R_M_sub : Subgroup M := R_K_sub.map K.subtype
  have he_inj : Function.Injective e.toMonoidHom := e.injective
  have hcard_R_K : Nat.card R_K_sub = Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) := by
    simpa [R_K_sub] using
      Subgroup.card_map_of_injective (K := (R : Subgroup (N ⊓ M : Subgroup G)))
        (f := e.toMonoidHom) he_inj
  have hcard_R_M : Nat.card R_M_sub = Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) := by
    have hcard_map : Nat.card R_M_sub = Nat.card R_K_sub := by
      simpa [R_M_sub] using
        Subgroup.card_map_of_injective (K := R_K_sub) (f := K.subtype) K.subtype_injective
    rw [hcard_map, hcard_R_K]
  have hR_K_p : IsPGroup p R_K_sub := IsPGroup.map R.isPGroup' e.toMonoidHom
  have hR_M_p : IsPGroup p R_M_sub := IsPGroup.map hR_K_p K.subtype
  rcases IsPGroup.exists_le_sylow hR_M_p with ⟨P', hR_le_P'⟩
  let R_P : Subgroup (P' : Subgroup M) := R_M_sub.subgroupOf (P' : Subgroup M)
  have hcard_R_P : Nat.card R_P = Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) := by
    calc
      Nat.card R_P = Nat.card R_M_sub :=
        natCard_subgroupOf_eq _ _ hR_le_P'
      _ = Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) := hcard_R_M
  have hR_P_lt_top : R_P < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    have hP'_le_R : (P' : Subgroup M) ≤ R_M_sub :=
      (Subgroup.subgroupOf_eq_top).1 htop
    have hR_eq_P' : R_M_sub = (P' : Subgroup M) := le_antisymm hR_le_P' hP'_le_R
    have hP'_card_eq_P : Nat.card (P' : Subgroup M) = Nat.card (P : Subgroup M) := by
      rw [Sylow.card_eq_multiplicity P', Sylow.card_eq_multiplicity P]
    have hnot :
        ¬ Nat.card (R : Subgroup (N ⊓ M : Subgroup G)) <
          Nat.card (P : Subgroup M) := by
      rw [← hP'_card_eq_P, ← hR_eq_P', hcard_R_M]
      exact lt_irrefl _
    exact hnot hcard_lt
  let NP : Subgroup (P' : Subgroup M) := Subgroup.normalizer (R_P : Set (P' : Subgroup M))
  let NP_M : Subgroup M := NP.map (P' : Subgroup M).subtype
  have hfact_RP_NP :
      Nat.factorization (Nat.card R_P) p < Nat.factorization (Nat.card NP) p :=
    section8_factorization_lt_normalizer_of_lt_top_in_pgroup P'.isPGroup' hR_P_lt_top
  have hR_P_image_M : section8SubgroupInAmbient (G := M) R_P = R_M_sub := by
    simpa [section8SubgroupInAmbient, R_P] using
      Subgroup.map_subgroupOf_eq_of_le hR_le_P'
  have hNP_M_le_norm_RM : NP_M ≤ Subgroup.normalizer (R_M_sub : Set M) := by
    have hnorm := section8_normalizer_subgroupInAmbient_le (G := M) R_P
    simpa [NP, NP_M, hR_P_image_M] using hnorm
  have hR_M_image_G : section8SubgroupInAmbient R_M_sub = R_G := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨xM, hxM_RM, rfl⟩
      change xM ∈ R_M_sub at hxM_RM
      rcases Subgroup.mem_map.mp hxM_RM with ⟨xK, hxK_RK, hxK_eq⟩
      rcases Subgroup.mem_map.mp hxK_RK with ⟨xR, hxR, hxR_eq⟩
      exact Subgroup.mem_map.mpr ⟨xR, hxR, by
        have hxKM : (xK : M) = xM := hxK_eq
        calc
          (xR : G) = (((e xR : K) : M) : G) := by rfl
          _ = (xK : G) := congrArg (fun z : K => ((z : M) : G)) hxR_eq
          _ = (xM : G) := congrArg Subtype.val hxKM⟩
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨xR, hxR, rfl⟩
      change ((xR : (N ⊓ M : Subgroup G)) : G) ∈ R_M_sub.map M.subtype
      refine Subgroup.mem_map.mpr ?_
      refine ⟨((e xR : K) : M), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem K.subtype (Subgroup.mem_map_of_mem e.toMonoidHom hxR)
      · rfl
  have hNP_G_le :
      NP_M.map M.subtype ≤
        (Subgroup.normalizer (R_G : Set G) ⊓ M : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxM_NP, rfl⟩
    constructor
    · have hx_norm_RM : xM ∈ Subgroup.normalizer (R_M_sub : Set M) :=
        hNP_M_le_norm_RM hxM_NP
      have hx_norm_map :
          ((xM : M) : G) ∈ (Subgroup.normalizer (R_M_sub : Set M)).map M.subtype :=
        Subgroup.mem_map_of_mem M.subtype hx_norm_RM
      have hx_norm_ambient :
          ((xM : M) : G) ∈ Subgroup.normalizer (section8SubgroupInAmbient R_M_sub : Set G) :=
        section8_normalizer_subgroupInAmbient_le R_M_sub hx_norm_map
      simpa [hR_M_image_G] using hx_norm_ambient
    · exact xM.property
  have hcard_NP_M : Nat.card NP_M = Nat.card NP := by
    simpa [NP_M] using
      Subgroup.card_map_of_injective (K := NP) (f := (P' : Subgroup M).subtype)
        (P' : Subgroup M).subtype_injective
  have hcard_NP_G : Nat.card (NP_M.map M.subtype) = Nat.card NP := by
    calc
      Nat.card (NP_M.map M.subtype) = Nat.card NP_M := by
        simpa using
          Subgroup.card_map_of_injective (K := NP_M) (f := M.subtype) M.subtype_injective
      _ = Nat.card NP := hcard_NP_M
  have hfact_NP_le :
      Nat.factorization (Nat.card NP) p ≤
        Nat.factorization
          (Nat.card (Subgroup.normalizer (R_G : Set G) ⊓ M : Subgroup G)) p := by
    rw [← hcard_NP_G]
    exact Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hNP_G_le) Nat.card_pos.ne' Nat.card_pos.ne'
  have hfact_inf_eq_RP :
      Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p =
        Nat.factorization (Nat.card R_P) p := by
    calc
      Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p =
          Nat.factorization (Nat.card (R : Subgroup (N ⊓ M : Subgroup G))) p :=
        (section8_factorization_card_sylow R).symm
      _ = Nat.factorization (Nat.card R_P) p := by rw [hcard_R_P]
  calc
    Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p =
        Nat.factorization (Nat.card R_P) p := hfact_inf_eq_RP
    _ < Nat.factorization (Nat.card NP) p := hfact_RP_NP
    _ ≤ Nat.factorization
        (Nat.card (Subgroup.normalizer (R_G : Set G) ⊓ M : Subgroup G)) p := hfact_NP_le

/-- The maximal-choice step in the unequal-order case of branch (b): if the normalizer of
the chosen Sylow subgroup has larger `p`-part after intersecting `M`, then that normalizer
must already lie in `M`. -/
public theorem CFSG.section8_inf_sylow_normalizer_le_of_factorization_gt
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M N A_G : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (R : Sylow p (N ⊓ M : Subgroup G))
    (hA_le_R : A_G ≤ section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)))
    (hR_ne_bot : section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) ≠ ⊥)
    (hmax :
      ∀ K : Subgroup G, K ∈ section8MaximalSubgroupsContaining A_G → K ≠ M →
        Nat.factorization (Nat.card (K ⊓ M : Subgroup G)) p ≤
          Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p)
    (hgt :
      Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p <
        Nat.factorization
          (Nat.card
            (Subgroup.normalizer
              (section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) : Set G) ⊓
                M : Subgroup G)) p) :
    Subgroup.normalizer
        (section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G)) : Set G) ≤ M := by
  let R_G : Subgroup G := section8SubgroupInAmbient (R : Subgroup (N ⊓ M : Subgroup G))
  let L : Subgroup G := Subgroup.normalizer (R_G : Set G)
  have hR_G_le_M : R_G ≤ M :=
    (section8SubgroupInAmbient_le (R : Subgroup (N ⊓ M : Subgroup G))).trans inf_le_right
  by_contra hL_not_le_M
  have hL_ne_top : L ≠ ⊤ := by
    intro hLtop
    have hRnorm : R_G.Normal := Subgroup.normalizer_eq_top_iff.mp hLtop
    let : IsSimpleGroup G := IsMinCE.simple
    rcases (haveI := hRnorm; IsSimpleGroup.eq_bot_or_eq_top_of_normal R_G) with hRbot | hRtop
    · exact hR_ne_bot (by simpa [R_G] using hRbot)
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [R_G, hRtop] using hR_G_le_M
      exact hM.1 (top_le_iff.mp htop_le_M)
  rcases eq_top_or_exists_le_coatom L with hLtop | ⟨K, hKcoatom, hLK⟩
  · exact hL_ne_top hLtop
  have hKmax : K ∈ section8MaximalSubgroups G := hKcoatom
  have hA_le_K : A_G ≤ K :=
    hA_le_R.trans (Subgroup.le_normalizer.trans hLK)
  have hKcont : K ∈ section8MaximalSubgroupsContaining A_G := ⟨hKmax, hA_le_K⟩
  have hK_ne_M : K ≠ M := by
    intro hKM
    exact hL_not_le_M (by simpa [hKM] using hLK)
  have hLKinf :
      L ⊓ M ≤ K ⊓ M := by
    exact inf_le_inf hLK le_rfl
  have hfact_LK :
      Nat.factorization (Nat.card (L ⊓ M : Subgroup G)) p ≤
        Nat.factorization (Nat.card (K ⊓ M : Subgroup G)) p :=
    Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hLKinf) Nat.card_pos.ne' Nat.card_pos.ne'
  have hfact_KN :
      Nat.factorization (Nat.card (K ⊓ M : Subgroup G)) p ≤
        Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p :=
    hmax K hKcont hK_ne_M
  have hnot :
      ¬ Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p <
        Nat.factorization (Nat.card (L ⊓ M : Subgroup G)) p :=
    not_lt_of_ge (hfact_LK.trans hfact_KN)
  exact hnot (by simpa [L, R_G] using hgt)

/-- Branch (b) maximal-overgroup uniqueness: every maximal overgroup of a transported
`SCN_3(P)` subgroup is `M`. -/
public theorem CFSG.section8_eq_maximalOver_sylowSubgroupInAmbient_of_fitting_isPGroup
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A)) :
    N = M := by
  by_contra hNM
  let A_G : Subgroup G := section8SylowSubgroupInAmbient M P A
  have hp_dvd_G : p ∣ Nat.card G :=
    (hpF : p ∣ Nat.card (section8FittingSubgroup M)).trans
      (Subgroup.card_subgroup_dvd_card (section8FittingSubgroup M))
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hA_G_ne_bot : A_G ≠ ⊥ := by
    simpa [A_G] using
      section8SylowSubgroupInAmbient_ne_bot_of_mem_scnSubgroups hpodd P hA
  rcases section8_exists_maximal_counterexample_inf_factorization
      (M := M) (A_G := A_G) (p := p) ⟨N, hN, hNM⟩ with
    ⟨H, hH, hHM, hmax⟩
  rcases section8_exists_sylow_inf_maximalOver_containing_sylowSubgroupInAmbient
      P (by simpa [A_G] using hH) with
    ⟨R, hA_le_R⟩
  have hR_ne_bot : section8SubgroupInAmbient (R : Subgroup (H ⊓ M : Subgroup G)) ≠ ⊥ := by
    intro hRbot
    have hA_bot : A_G = ⊥ :=
      le_bot_iff.mp (by simpa [hRbot] using hA_le_R)
    exact hA_G_ne_bot hA_bot
  have hnorm :
      Subgroup.normalizer
          (section8SubgroupInAmbient (R : Subgroup (H ⊓ M : Subgroup G)) : Set G) ≤ M := by
    by_cases hlt :
        Nat.card (R : Subgroup (H ⊓ M : Subgroup G)) < Nat.card (P : Subgroup M)
    · have hgt :
        Nat.factorization (Nat.card (H ⊓ M : Subgroup G)) p <
          Nat.factorization
            (Nat.card
              (Subgroup.normalizer
                (section8SubgroupInAmbient (R : Subgroup (H ⊓ M : Subgroup G)) : Set G) ⊓
                  M : Subgroup G)) p :=
        section8_inf_sylow_normalizer_factorization_gt_of_card_lt P R hlt
      exact
        section8_inf_sylow_normalizer_le_of_factorization_gt
          hM R hA_le_R hR_ne_bot hmax hgt
    · have hle :
        Nat.card (R : Subgroup (H ⊓ M : Subgroup G)) ≤ Nat.card (P : Subgroup M) :=
        section8_inf_sylow_card_le_sylow P R
      have hge :
        Nat.card (P : Subgroup M) ≤ Nat.card (R : Subgroup (H ⊓ M : Subgroup G)) :=
        le_of_not_gt hlt
      have hcard :
        Nat.card (R : Subgroup (H ⊓ M : Subgroup G)) = Nat.card (P : Subgroup M) :=
        le_antisymm hle hge
      exact
        section8_inf_sylow_normalizer_le_of_card_eq_sylowSubgroupInAmbient
          hM hpF hFp P R hcard
  have hHM_eq : H = M :=
    section8_eq_maximalOver_sylowSubgroupInAmbient_of_inf_sylow_normalizer_le
      hM hpF hFp P hA hH R hnorm
  exact hHM hHM_eq

/-- Branch (b) normalizer control for each transported `SCN_3(P)` subgroup. -/
public theorem CFSG.section8_maximalOver_sylowSubgroupInAmbient_le_normalizer_fitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    {N : Subgroup G}
    (hN : N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A)) :
    N ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
  have hNM : N = M :=
    section8_eq_maximalOver_sylowSubgroupInAmbient_of_fitting_isPGroup
      hM hpF hFp P hA hN
  rw [hNM]
  let : ((section8FittingSubgroup M).subgroupOf M).Normal :=
    section8FittingSubgroup_normal_in M
  exact Subgroup.le_normalizer_of_normal_subgroupOf (section8FittingSubgroup_le M)


/-- If \(p \in \pi(F(M))\), then \(N_G(F(M)) = M\). -/
public theorem CFSG.section8_normalizer_fittingSubgroup_eq
      [Finite G] [IsMinCE G] {M : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section8MaximalSubgroups G)
    (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M)) :
    Subgroup.normalizer (section8FittingSubgroup M : Set G) = M :=
  section8_normalizer_eq_of_nontrivial_normal_in_maximal hM
    (section8FittingSubgroup_le M) (section8_ne_bot_of_mem_subgroupPrimeSet hqF)
    (section8FittingSubgroup_normal_in M)

/-- An endpoint criterion for Section 8: normalizer control by `F(M)` gives membership in `U`. -/
public theorem CFSG.section8UniqueSubgroups_of_le_fitting_and_forall_le_normalizer_fitting
    [Finite G] [IsMinCE G] {H M : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section8MaximalSubgroups G)
    (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hHF : H ≤ section8FittingSubgroup M)
    (hNnorm :
      ∀ N : Subgroup G, N ∈ section8MaximalSubgroupsContaining H →
        N ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G)) :
    H ∈ section8UniqueSubgroups G :=
  section8UniqueSubgroups_of_forall_le_normalizer_eq
    (section8_ne_top_of_le_maximal hM (hHF.trans (section8FittingSubgroup_le M)))
    hM (hHF.trans (section8FittingSubgroup_le M))
    (section8_normalizer_fittingSubgroup_eq hM hqF) hNnorm

/-- The endpoint criterion specialized to `C_{F(M)}(A₀)`. -/
public theorem CFSG.section8CentralizerInFitting_unique_of_forall_le_normalizer_fitting
    [Finite G] [IsMinCE G] {M : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section8MaximalSubgroups G)
    (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (A₀ : Subgroup (section8FittingSubgroup M))
    (hNnorm :
      ∀ N : Subgroup G,
        N ∈ section8MaximalSubgroupsContaining (section8CentralizerInFitting M A₀) →
          N ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G)) :
    section8CentralizerInFitting M A₀ ∈ section8UniqueSubgroups G :=
  section8UniqueSubgroups_of_le_fitting_and_forall_le_normalizer_fitting
    hM hqF (section8CentralizerInFitting_le M A₀) hNnorm

/-- The endpoint criterion specialized to subgroups transported from a Sylow subgroup of `M`. -/
public theorem CFSG.section8SylowSubgroupInAmbient_unique_of_forall_le_normalizer_fitting
    [Finite G] [IsMinCE G] {M : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section8MaximalSubgroups G)
    (hqF : q ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {p : ℕ} (P : Sylow p M) (A : Subgroup (P : Subgroup M))
    (hAF : section8SylowSubgroupInAmbient M P A ≤ section8FittingSubgroup M)
    (hNnorm :
      ∀ N : Subgroup G,
        N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A) →
          N ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G)) :
    section8SylowSubgroupInAmbient M P A ∈ section8UniqueSubgroups G :=
  section8UniqueSubgroups_of_le_fitting_and_forall_le_normalizer_fitting
    hM hqF hAF hNnorm

/-- The final `SCN_3(P)` endpoint in part (b), isolated from the remaining normalizer-control step. -/
public theorem CFSG.section8_part_b_scn_endpoint
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) {A : Subgroup (P : Subgroup M)}
    (hA : A ∈ scnSubgroups 3 (P : Subgroup M))
    (hNnorm :
      ∀ N : Subgroup G,
        N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A) →
          N ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G)) :
    section8SylowSubgroupInAmbient M P A ≤ section8FittingSubgroup M ∧
      section8SylowSubgroupInAmbient M P A ∈ section8UniqueSubgroups G := by
  have hAF : section8SylowSubgroupInAmbient M P A ≤ section8FittingSubgroup M :=
    section8SylowSubgroupInAmbient_le_fitting_of_isPGroup hM hFp P hA
  exact ⟨hAF,
    section8SylowSubgroupInAmbient_unique_of_forall_le_normalizer_fitting
      hM hpF P A hAF hNnorm⟩

/-- Branch (b), reduced to the remaining maximal-overgroup normalizer-control step for each
transported `SCN_3(P)` subgroup. -/
public theorem CFSG.section8_part_b_core_of_forall_scn_le_normalizer_fitting
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M)
    (hNnorm :
      ∀ A : Subgroup (P : Subgroup M),
        A ∈ scnSubgroups 3 (P : Subgroup M) →
          ∀ N : Subgroup G,
            N ∈ section8MaximalSubgroupsContaining (section8SylowSubgroupInAmbient M P A) →
              N ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G)) :
    (∃ P₀ : Sylow p G,
      (P₀ : Subgroup G) = section8SubgroupInAmbient (P : Subgroup M)) ∧
      ∀ A : Subgroup (P : Subgroup M),
        A ∈ scnSubgroups 3 (P : Subgroup M) →
          section8SylowSubgroupInAmbient M P A ≤ section8FittingSubgroup M ∧
            section8SylowSubgroupInAmbient M P A ∈ section8UniqueSubgroups G := by
  constructor
  · exact section8_part_b_sylow_core hM hpF hFp P
  · intro A hA
    exact section8_part_b_scn_endpoint hM hpF hFp P hA (hNnorm A hA)

/-- Branch (b) of Theorem 8.1. -/
public theorem CFSG.theorem_8_1_part_b_core
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    (hFp : IsPGroup p (section8FittingSubgroup M))
    (P : Sylow p M) :
    (∃ P₀ : Sylow p G,
      (P₀ : Subgroup G) = section8SubgroupInAmbient (P : Subgroup M)) ∧
      ∀ A : Subgroup (P : Subgroup M),
        A ∈ scnSubgroups 3 (P : Subgroup M) →
          section8SylowSubgroupInAmbient M P A ≤ section8FittingSubgroup M ∧
            section8SylowSubgroupInAmbient M P A ∈ section8UniqueSubgroups G :=
  section8_part_b_core_of_forall_scn_le_normalizer_fitting hM hpF hFp P
    (by
      intro A hA N hN
      exact section8_maximalOver_sylowSubgroupInAmbient_le_normalizer_fitting
        hM hpF hFp P hA hN)


/-- Branch (a) of Theorem 8.1. -/
public theorem CFSG.theorem_8_1_part_a_core
    [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (hnFp : ¬ IsPGroup p (section8FittingSubgroup M)) :
    section8CentralizerInFitting M A₀ ∈ section8UniqueSubgroups G := by
  exact section8CentralizerInFitting_unique_of_forall_le_normalizer_fitting
    hM hpF A₀ (by
      intro N hN
      exact section8CentralizerInFitting_maximal_overgroups_le_normalizer_fitting
        hM hpF hA₀ hA₀rank hnFp hN)

end Notation

section Section8

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 8.1. -/
public theorem CFSG.theorem_8_1
    {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section8MaximalSubgroups G)
    (hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet (section8FittingSubgroup M))
    {A₀ : Subgroup (section8FittingSubgroup M)}
    (hA₀ : A₀ ∈ maximalElementaryAbelianSubgroups p (section8FittingSubgroup M))
    (hA₀rank : 3 ≤ generatorRank A₀)
    (P : Sylow p M) :
    (¬ IsPGroup p (section8FittingSubgroup M) →
        section8CentralizerInFitting M A₀ ∈ section8UniqueSubgroups G) ∧
      (IsPGroup p (section8FittingSubgroup M) →
        (∃ P₀ : Sylow p G,
          (P₀ : Subgroup G) = section8SubgroupInAmbient (P : Subgroup M)) ∧
          ∀ A : Subgroup (P : Subgroup M),
            A ∈ scnSubgroups 3 (P : Subgroup M) →
              section8SylowSubgroupInAmbient M P A ≤ section8FittingSubgroup M ∧
                section8SylowSubgroupInAmbient M P A ∈ section8UniqueSubgroups G) := by
  constructor
  · intro hnFp
    exact theorem_8_1_part_a_core hM hpF hA₀ hA₀rank hnFp
  · intro hFp
    exact theorem_8_1_part_b_core hM hpF hFp P

end Section8
