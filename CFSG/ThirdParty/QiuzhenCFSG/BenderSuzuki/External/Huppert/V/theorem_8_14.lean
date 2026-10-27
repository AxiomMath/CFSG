module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_6_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.Semidirect
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.SamePrime
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.ComplementTransfer

namespace CFSG
end CFSG
open CFSG

/-!
# Thompson fixed-point-free nilpotence interfaces

This file records statement-only external theorem interfaces for Thompson's
fixed-point-free automorphism theorem as used in Peterfalvi, Part II, Chapter I.

Source guide: `docs/PFpart2/ref/PFpart2_external_formalization_guides.md`,
item `ThompsonFixedPointFreeNilpotence`; Huppert, *Endliche Gruppen I*,
V.8.14.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

attribute [local instance] commutatorElement

universe u v

set_option maxHeartbeats 0

private theorem hkt_local_sylow_map_eq_ambient_of_normalizer_top
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {U : Subgroup Q} (S : Sylow q Q)
    (P : Sylow q (Subgroup.normalizer (U : Set Q)))
    (hNtop : Subgroup.normalizer (U : Set Q) = ⊤)
    (hPmap_le_S :
      (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
          (Subgroup.normalizer (U : Set Q)).subtype ≤ (S : Subgroup Q)) :
    (P : Subgroup (Subgroup.normalizer (U : Set Q))).map
        (Subgroup.normalizer (U : Set Q)).subtype = (S : Subgroup Q) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  let Pmap : Subgroup Q := (P : Subgroup N).map N.subtype
  have hNtop' : N = ⊤ := by simpa [N] using hNtop
  have hcardN : Nat.card N = Nat.card Q := by
    simp [hNtop']
  have hPmap_card : Nat.card Pmap = Nat.card (P : Subgroup N) := by
    simpa [Pmap, N] using
      Subgroup.card_map_of_injective
        (K := (P : Subgroup N)) (f := N.subtype) N.subtype_injective
  have hP_card_S : Nat.card (P : Subgroup N) = Nat.card (S : Subgroup Q) := by
    rw [Sylow.card_eq_multiplicity P, Sylow.card_eq_multiplicity S, hcardN]
  apply Subgroup.eq_of_le_of_card_ge
    (show Pmap ≤ (S : Subgroup Q) from by simpa [Pmap, N] using hPmap_le_S)
  rw [hPmap_card, hP_card_S]


/-- A single `q`-element generates a `q`-group.  This tiny generator lemma is
used in the Huppert IV.6.2(f)--(r) p-core absorption argument, where one tests
whether adjoining a `q`-element to `O_q(Q)` gives a larger `q`-subgroup. -/
private theorem hkt_zpowers_isPGroup_of_isPElement
    {Q : Type u} [Group Q] {q : ℕ} [Fact q.Prime] {x : Q}
    (hx : IsPElement (p := q) x) :
    IsPGroup q (Subgroup.zpowers x) := by
  rcases hx with ⟨n, hn⟩
  refine IsPGroup.of_card (p := q) (G := Subgroup.zpowers x) (n := n) ?_
  simpa [Nat.card_zpowers] using hn

/-- Adjoining a `q`-element to the normal `q`-core still gives a `q`-subgroup.
This is the formal first step of the IV.6.2 absorption route, before the
maximality argument is used to force the generated subgroup back into the core. -/
private theorem hkt_pCore_sup_zpowers_isPGroup_of_isPElement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime] {x : Q}
    (hx : IsPElement (p := q) x) :
    IsPGroup q (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) := by
  exact IsPGroup.to_sup_of_normal_left
    (p := q) (H := pCore q Q) (K := Subgroup.zpowers x)
    (pCore_isPGroup (G := Q) (p := q))
    (hkt_zpowers_isPGroup_of_isPElement (Q := Q) (q := q) hx)

/-- If the tested `q`-element is not already in `O_q(Q)`, adjoining its cyclic
subgroup strictly enlarges the core. -/
private theorem hkt_pCore_lt_sup_zpowers_of_not_mem
    {Q : Type u} [Group Q] {q : ℕ} {x : Q}
    (hx_not : x ∉ pCore q Q) :
    pCore q Q < (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro hsup_eq
  exact hx_not (by
    have hx_zpow : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    have hx_sup : x ∈ (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) :=
      show x ∈ (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) from
        (le_sup_right : Subgroup.zpowers x ≤
          (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q)) hx_zpow
    rw [← hsup_eq] at hx_sup
    exact hx_sup)

/-- Cardinal form of `hkt_pCore_lt_sup_zpowers_of_not_mem`, convenient for the
Huppert score comparison. -/
private theorem hkt_card_pCore_lt_sup_zpowers_of_not_mem
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} {x : Q}
    (hx_not : x ∉ pCore q Q) :
    Nat.card (pCore q Q) <
      Nat.card (pCore q Q ⊔ Subgroup.zpowers x : Subgroup Q) :=
  natCard_lt_of_subgroup_lt (G := Q)
    (hkt_pCore_lt_sup_zpowers_of_not_mem (Q := Q) (q := q) hx_not)

/-- The normal `q`-core lies in every Sylow `q`-subgroup. -/
private theorem hkt_pCore_le_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    pCore q Q ≤ (S : Subgroup Q) := by
  have hsup_p : IsPGroup q ((S : Subgroup Q) ⊔ pCore q Q : Subgroup Q) :=
    IsPGroup.to_sup_of_normal_right (p := q) (H := (S : Subgroup Q))
      (K := pCore q Q) S.isPGroup' (pCore_isPGroup (G := Q) (p := q))
  have hsup_eq : (S : Subgroup Q) ⊔ pCore q Q = (S : Subgroup Q) :=
    S.is_maximal' hsup_p le_sup_left
  exact le_sup_right.trans (le_of_eq hsup_eq)

/-- A `q`-subgroup normalized by a fixed Sylow `q`-subgroup is contained in
that Sylow subgroup. -/
private theorem hkt_normalized_pSubgroup_le_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {A : Subgroup Q}
    (hAp : IsPGroup q A)
    (hS_le_norm_A : (S : Subgroup Q) ≤ Subgroup.normalizer (A : Set Q)) :
    A ≤ (S : Subgroup Q) := by
  have hsup_p : IsPGroup q ((S : Subgroup Q) ⊔ A : Subgroup Q) :=
    IsPGroup.to_sup_of_normal_right'
      (G := Q) (H := (S : Subgroup Q)) (K := A)
      S.isPGroup' hAp hS_le_norm_A
  have hsup_eq : (S : Subgroup Q) ⊔ A = (S : Subgroup Q) :=
    S.is_maximal' hsup_p le_sup_left
  exact le_sup_right.trans (le_of_eq hsup_eq)

/-- If a tested `q`-element already lies in a fixed Sylow subgroup, then the
 test subgroup `O_q(Q)⟨y⟩` also lies in that Sylow subgroup. -/
private theorem hkt_pCore_sup_zpowers_le_sylow_of_mem
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {y : Q} (hyS : y ∈ (S : Subgroup Q)) :
    pCore q Q ⊔ Subgroup.zpowers y ≤ (S : Subgroup Q) := by
  refine sup_le (hkt_pCore_le_sylow (Q := Q) (q := q) S) ?_
  exact Subgroup.zpowers_le.2 hyS

/-- If every commutator `[z,s]` with `s ∈ S` lies in the normal `q`-core,
then `S` normalizes the subgroup generated by the `q`-core and `z`. -/
private theorem hkt_pCore_sup_zpowers_le_normalizer_of_comm_mod_core
    {Q : Type u} [Group Q] {q : ℕ} {z : Q} {S : Subgroup Q}
    (hcomm : ∀ s : Q, s ∈ S → ⁅z, s⁆ ∈ pCore q Q) :
    S ≤ Subgroup.normalizer ((pCore q Q ⊔ Subgroup.zpowers z : Subgroup Q) : Set Q) := by
  classical
  let W : Subgroup Q := pCore q Q ⊔ Subgroup.zpowers z
  have hconj_z : ∀ s : Q, s ∈ S → s * z * s⁻¹ ∈ W := by
    intro s hs
    have hcomm_inv : ⁅z, s⁆⁻¹ ∈ pCore q Q :=
      (pCore q Q).inv_mem (hcomm s hs)
    refine (Subgroup.mem_sup_of_normal_left
      (s := pCore q Q) (t := Subgroup.zpowers z) (x := s * z * s⁻¹)).2 ?_
    refine ⟨⁅z, s⁆⁻¹, hcomm_inv, z, Subgroup.mem_zpowers z, ?_⟩
    simp [commutatorElement_def, mul_assoc]
  have hforward :
      ∀ s : Q, s ∈ S → ∀ x : Q, x ∈ W → s * x * s⁻¹ ∈ W := by
    intro s hs x hx
    rcases (Subgroup.mem_sup_of_normal_left
        (s := pCore q Q) (t := Subgroup.zpowers z) (x := x)).1 (by simpa [W] using hx) with
      ⟨c, hc, k, hk, rfl⟩
    have hc_conj : s * c * s⁻¹ ∈ pCore q Q :=
      (pCore_normal (G := Q) (p := q)).conj_mem c hc s
    have hk_conj : s * k * s⁻¹ ∈ W := by
      rcases Subgroup.mem_zpowers_iff.mp hk with ⟨n, rfl⟩
      simpa [conj_zpow, W] using (W.zpow_mem (hconj_z s hs) n)
    have hmul : (s * c * s⁻¹) * (s * k * s⁻¹) ∈ W :=
      W.mul_mem ((show pCore q Q ≤ W from by simp [W]) hc_conj) hk_conj
    simpa [mul_assoc] using hmul
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hforward s hs x (by simpa [W] using hx)
  · intro hx
    have hx' : s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ ∈ W :=
      hforward s⁻¹ (S.inv_mem hs) (s * x * s⁻¹) (by simpa [W] using hx)
    simpa [mul_assoc, W] using hx'

/-- If an element centralizes the generator `z` modulo `O_q(Q)`, then it
centralizes every element of `O_q(Q)⟨z⟩` modulo `O_q(Q)`.  This is the quotient
centralizer form of the local IV.6.2 normalizer-action bridge. -/
private theorem hkt_pCore_sup_zpowers_comm_mod_core_of_generator
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {z n w : Q}
    (hzn : ⁅z, n⁆ ∈ pCore q Q)
    (hw : w ∈ (pCore q Q ⊔ Subgroup.zpowers z : Subgroup Q)) :
    ⁅w, n⁆ ∈ pCore q Q := by
  classical
  let N : Subgroup Q := pCore q Q
  letI : N.Normal := by
    simpa [N] using (pCore_normal (G := Q) (p := q))
  let π : Q →* Q ⧸ N := QuotientGroup.mk' N
  let C : Subgroup Q :=
    (Subgroup.centralizer ({π n} : Set (Q ⧸ N))).comap π
  have hN_le_C : N ≤ C := by
    intro a ha
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = π n := by simpa using hy
    subst y
    simp [π, (QuotientGroup.eq_one_iff (N := N) (x := a)).2 ha]
  have hzC : z ∈ C := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = π n := by simpa using hy
    subst y
    have hcomm_q : ⁅π z, π n⁆ = 1 := by
      have hmk : π ⁅z, n⁆ = 1 :=
        (QuotientGroup.eq_one_iff (N := N) (x := ⁅z, n⁆)).2 (by
          simpa [N] using hzn)
      simpa [π] using
        (show π ⁅z, n⁆ = ⁅π z, π n⁆ from
          map_commutatorElement (f := π) (g₁ := z) (g₂ := n)).symm.trans hmk
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm_q).symm
  have hW_le_C : (pCore q Q ⊔ Subgroup.zpowers z : Subgroup Q) ≤ C := by
    refine sup_le ?_ ?_
    · intro a ha
      exact hN_le_C (by simpa [N] using ha)
    · exact Subgroup.zpowers_le.2 hzC
  have hwC : w ∈ C := hW_le_C hw
  have hwcent : π w ∈ Subgroup.centralizer ({π n} : Set (Q ⧸ N)) := by
    simpa [C] using hwC
  have hmul : π w * π n = π n * π w :=
    ((Subgroup.mem_centralizer_iff.mp hwcent) (π n) (by simp)).symm
  have hcomm_q : ⁅π w, π n⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hmul
  have hmk : π ⁅w, n⁆ = 1 := by
    simpa [π] using
      (show π ⁅w, n⁆ = ⁅π w, π n⁆ from
        map_commutatorElement (f := π) (g₁ := w) (g₂ := n)).trans hcomm_q
  have hwN : ⁅w, n⁆ ∈ N :=
    (QuotientGroup.eq_one_iff (N := N) (x := ⁅w, n⁆)).1 hmk
  simpa [N] using hwN

/-- A `q`-element can be conjugated into any fixed Sylow `q`-subgroup. -/
private theorem hkt_exists_conj_mem_sylow_of_isPElement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {x : Q} (hx : IsPElement (p := q) x) :
    ∃ g : Q, g * x * g⁻¹ ∈ (S : Subgroup Q) := by
  classical
  have hZp : IsPGroup q (Subgroup.zpowers x) :=
    hkt_zpowers_isPGroup_of_isPElement (Q := Q) (q := q) hx
  obtain ⟨T, hZ_le_T⟩ := IsPGroup.exists_le_sylow (G := Q) (p := q) hZp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q T S
  have hconjT_eq_S :
      (MulAut.conj g • (T : Subgroup Q) : Subgroup Q) = (S : Subgroup Q) := by
    calc
      (MulAut.conj g • (T : Subgroup Q) : Subgroup Q) =
          ((g • T : Sylow q Q) : Subgroup Q) := by
            rw [← Sylow.coe_subgroup_smul (g := g) (P := T)]
      _ = (S : Subgroup Q) := by simp [hg]
  have hxT : x ∈ (T : Subgroup Q) :=
    hZ_le_T (Subgroup.mem_zpowers x)
  have hxConjT :
      (MulAut.conj g) x ∈ (MulAut.conj g • (T : Subgroup Q) : Subgroup Q) :=
    Set.mem_smul_set.mpr ⟨x, hxT, rfl⟩
  exact ⟨g, by simpa [MulAut.conj_apply, hconjT_eq_S] using hxConjT⟩

/-- If a conjugate of an element lies in the `q`-core, then the element itself
lies in the `q`-core. -/
private theorem hkt_mem_pCore_of_conj_mem
    {Q : Type u} [Group Q] {q : ℕ} {g x : Q}
    (hx : g * x * g⁻¹ ∈ pCore q Q) :
    x ∈ pCore q Q := by
  have hx_back :
      g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ ∈ pCore q Q :=
    (pCore_normal (G := Q) (p := q)).conj_mem (g * x * g⁻¹) hx g⁻¹
  simpa [mul_assoc] using hx_back

/-- To absorb all ambient `q`-elements into `O_q(Q)`, it is enough to absorb
the `q`-elements that already lie in a fixed Sylow subgroup. -/
private theorem hkt_isPElement_mem_pCore_of_sylow_absorption
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hS :
      ∀ y : Q, y ∈ (S : Subgroup Q) → IsPElement (p := q) y → y ∈ pCore q Q)
    {x : Q} (hx : IsPElement (p := q) x) :
    x ∈ pCore q Q := by
  classical
  obtain ⟨g, hgS⟩ := hkt_exists_conj_mem_sylow_of_isPElement (Q := Q) (q := q) S hx
  have hgx_p : IsPElement (p := q) (g * x * g⁻¹) := by
    simpa [MulAut.conj_apply] using
      (isPElement_aut_iff (G := Q) (p := q) (MulAut.conj g) x).2 hx
  exact hkt_mem_pCore_of_conj_mem (Q := Q) (q := q) (g := g) (x := x)
    (hS (g * x * g⁻¹) hgS hgx_p)

/--
The Thompson IV.6.2 local endpoint needed in Huppert V.8.13 step 4 after an
invariant Sylow subgroup for an odd prime divisor has been chosen.
-/
private theorem hkt_has_normal_p_complement_of_invariant_odd_sylow
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {q : ℕ}
    [Fact q.Prime]
    (hq2 : q ≠ 2) (S : Sylow q Q)
    (hproper_invariant_subgroup_nil :
      ∀ N : Subgroup Q, N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent N)
    (hnormalizer_rank :
      HasNormalPComplement q
        (Subgroup.normalizer
          (huppertRankThompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)))
    (hnormalizer_ne_bot :
      Subgroup.normalizer
        (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊥)
    (hnormalizer_ne_top :
      Subgroup.normalizer
        (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (hnormalizerφ :
      ∀ x : Q,
        x ∈ Subgroup.normalizer
            (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ↔
          φ x ∈ Subgroup.normalizer
            (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))
    (hcentralizer_ne_bot :
      Subgroup.centralizer
        (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊥)
    (hcentralizer_ne_top :
      Subgroup.centralizer
        (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcentralizerφ :
      ∀ x : Q,
        x ∈ Subgroup.centralizer
            (centerIn (G := Q) (S : Subgroup Q) : Set Q) ↔
          φ x ∈ Subgroup.centralizer
            (centerIn (G := Q) (S : Subgroup Q) : Set Q)) :
    HasNormalPComplement q Q := by
  have hnormalizer :
      HasNormalPComplement q
        (↥(Subgroup.normalizer
          (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))) :=
    hkt_normalizer_thompsonSubgroup_has_normal_p_complement_of_invariant_odd_sylow
      φ S hproper_invariant_subgroup_nil hnormalizer_ne_bot
      hnormalizer_ne_top hnormalizerφ
  have hcentralizer :
      HasNormalPComplement q
        (↥(Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q))) :=
    hkt_centralizer_center_sylow_has_normal_p_complement_of_invariant_odd_sylow
      φ S hproper_invariant_subgroup_nil hcentralizer_ne_bot
      hcentralizer_ne_top hcentralizerφ
  exact huppert_IV_6_2_thompson_normal_p_complement
    (Q := Q) (q := q) hq2 S hcentralizer hnormalizer hnormalizer_rank

/--
The non-2-group branch of the HKT odd-prime core.  The Sylow choice is now
formalized; only the post-choice Thompson local endpoint remains.
-/
private theorem hkt_nilpotent_of_odd_prime_period_product_identity_not_two_group
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hnot_two : ¬ IsPGroup 2 Q) :
    Group.IsNilpotent Q := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (R : Type u) [Group R] [Finite R], (ψ : MulAut R) →
      Nat.card R = n →
      (fun r : R => ψ r)^[p] = id →
      (∀ r : R,
        ((List.range p).map (fun k ↦ (fun r : R => ψ r)^[k] r)).prod = 1) →
      ¬ IsPGroup 2 R → Group.IsNilpotent R
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih R _ _ ψ hcardR hperiodR hprodR hnot_twoR
    by_contra hnon_nilR
    have hproper_invariant_subgroup_nil :
        ∀ N : Subgroup R, N ≠ ⊥ → N ≠ ⊤ →
          (∀ r : R, r ∈ N ↔ ψ r ∈ N) → Group.IsNilpotent N := by
      intro N hNbot hNtop hNψ
      by_cases hNtwo : IsPGroup 2 N
      · exact hNtwo.isNilpotent
      · have hperiodN :
            (fun n : N => invariantSubgroupAut ψ N hNψ n)^[p] = id := by
          funext x
          apply Subtype.ext
          have hx := congrFun hperiodR (x : R)
          simpa [invariantSubgroupAut_iterate_coe ψ N hNψ p x] using hx
        have hprodN :
            ∀ n : N,
              ((List.range p).map
                (fun k ↦
                  (fun n : N => invariantSubgroupAut ψ N hNψ n)^[k] n)).prod = 1 :=
          hkt_product_identity_of_invariant_subgroup ψ N hNψ hprodR
        have hcard_lt : Nat.card N < Nat.card R := by
          have hlt : N < (⊤ : Subgroup R) := lt_top_iff_ne_top.mpr hNtop
          simpa using natCard_lt_of_subgroup_lt (G := R) hlt
        exact ih (Nat.card N) (by simpa [hcardR] using hcard_lt) N
          (invariantSubgroupAut ψ N hNψ) rfl hperiodN hprodN hNtwo
    have hproper_invariant_quotient_nil :
        ∀ N : Subgroup R, [N.Normal] → N ≠ ⊥ → N ≠ ⊤ →
          (∀ r : R, r ∈ N ↔ ψ r ∈ N) → Group.IsNilpotent (R ⧸ N) := by
      intro N hNnormal hNbot _hNtop hNψ
      by_cases hQtwo : IsPGroup 2 (R ⧸ N)
      · exact hQtwo.isNilpotent
      · have hperiodQ :
            (fun x : R ⧸ N => invariantQuotientAut ψ N hNψ x)^[p] = id := by
          funext x
          rcases QuotientGroup.mk'_surjective N x with ⟨r, rfl⟩
          rw [invariantQuotientAut_iterate_mk' ψ N hNψ p r]
          exact congrArg (QuotientGroup.mk' N) (congrFun hperiodR r)
        have hprodQ :
            ∀ x : R ⧸ N,
              ((List.range p).map
                (fun k ↦
                  (fun x : R ⧸ N => invariantQuotientAut ψ N hNψ x)^[k] x)).prod = 1 :=
          hkt_product_identity_of_invariant_quotient ψ N hNψ hprodR
        have hcard_lt : Nat.card (R ⧸ N) < Nat.card R :=
          natCard_quotient_lt_natCard_of_ne_bot N hNbot
        exact ih (Nat.card (R ⧸ N)) (by simpa [hcardR] using hcard_lt) (R ⧸ N)
          (invariantQuotientAut ψ N hNψ) rfl hperiodQ hprodQ hQtwo
    have hcenter_bot : Subgroup.center R = ⊥ := by
      apply hkt_center_eq_bot_of_minimal_branch hnon_nilR
      intro hcenter_ne_bot
      exact hproper_invariant_quotient_nil (Subgroup.center R)
        hcenter_ne_bot (hkt_center_ne_top_of_not_nilpotent hnon_nilR)
        (hkt_center_invariant ψ)
    have hnot_solvable : ¬ IsSolvable R :=
      hkt_nonsolvable_of_minimal_branch ψ hprime hp2 hperiodR hprodR hnon_nilR
        hproper_invariant_subgroup_nil hproper_invariant_quotient_nil hcenter_bot
    rcases hkt_exists_invariant_odd_sylow_of_not_two_group ψ hprime hp2 hperiodR hnot_twoR with
      ⟨q, hqprime, hq2, hq_dvd, S, hSψ⟩
    letI : Fact q.Prime := ⟨hqprime⟩
    let N : Subgroup R :=
      Subgroup.normalizer (thompsonSubgroup (G := R) (S : Subgroup R) : Set R)
    let C : Subgroup R :=
      Subgroup.centralizer (centerIn (G := R) (S : Subgroup R) : Set R)
    have hchar_simple :
        ∀ N : Subgroup R, N.Characteristic → N = ⊥ ∨ N = ⊤ :=
      hkt_characteristically_simple_of_minimal_branch
        ψ hnot_solvable hproper_invariant_subgroup_nil
        hproper_invariant_quotient_nil
    have hnormalizer_ne_bot : N ≠ ⊥ := by
      have hS_ne_bot : (S : Subgroup R) ≠ ⊥ :=
        Sylow.ne_bot_of_dvd_card (G := R) (p := q) S hq_dvd
      have hJ_ne_bot : thompsonSubgroup (G := R) (S : Subgroup R) ≠ ⊥ :=
        section8_thompsonSubgroup_ne_bot_of_ne_bot hS_ne_bot
      intro hNbot
      have hJ_le_bot : thompsonSubgroup (G := R) (S : Subgroup R) ≤ (⊥ : Subgroup R) := by
        rw [← hNbot]
        simpa [N] using
          (Subgroup.le_normalizer :
            thompsonSubgroup (G := R) (S : Subgroup R) ≤
              Subgroup.normalizer
                (thompsonSubgroup (G := R) (S : Subgroup R) : Set R))
      exact hJ_ne_bot (le_bot_iff.mp hJ_le_bot)
    have hnormalizer_ne_top : N ≠ ⊤ := by
      simpa [N] using
        hkt_normalizer_thompsonSubgroup_ne_top_of_characteristically_simple
          S hq_dvd hnot_solvable hchar_simple
    have hnormalizerψ : ∀ x : R, x ∈ N ↔ ψ x ∈ N := by
      have hJψ :
          ∀ x : R,
            x ∈ thompsonSubgroup (G := R) (S : Subgroup R) ↔
              ψ x ∈ thompsonSubgroup (G := R) (S : Subgroup R) :=
        hkt_thompsonSubgroup_invariant_of_invariant_sylow ψ S hSψ
      simpa [N] using hkt_normalizer_invariant_of_invariant ψ
        (thompsonSubgroup (G := R) (S : Subgroup R)) hJψ
    let Jrank : Subgroup R :=
      huppertRankThompsonSubgroup (G := R) (S : Subgroup R)
    let Nrank : Subgroup R := Subgroup.normalizer (Jrank : Set R)
    have hJrank_le_S : Jrank ≤ (S : Subgroup R) := by
      simpa [Jrank] using
        huppertRankThompsonSubgroup_le (G := R) (S : Subgroup R)
    have hJrank_ne_bot : Jrank ≠ ⊥ := by
      have hfamily_nonempty :
          ∃ A : Subgroup R,
            A ∈ huppertRankThompsonAbelianSubgroups
              (G := R) (S : Subgroup R) := by
        let candidates : Set (Subgroup R) :=
          {A : Subgroup R | A ≤ (S : Subgroup R) ∧ IsMulCommutative A}
        have hcandidates_nonempty : candidates.Nonempty := by
          refine ⟨⊥, ?_⟩
          exact ⟨bot_le, inferInstance⟩
        have hcandidates_finite : candidates.Finite := Set.toFinite candidates
        obtain ⟨A, hA, hAmax⟩ :=
          hcandidates_finite.exists_maximalFor
            (f := fun A : Subgroup R => generatorRank A)
            candidates hcandidates_nonempty
        rcases hA with ⟨hA_le_S, hA_comm⟩
        refine ⟨A, hA_le_S, hA_comm, ?_⟩
        intro B hB_le_S hB_comm
        by_cases hle : generatorRank A ≤ generatorRank B
        · exact hAmax ⟨hB_le_S, hB_comm⟩ hle
        · exact Nat.le_of_not_ge hle
      obtain ⟨A, hA⟩ := hfamily_nonempty
      let Z : Subgroup R := centerIn (G := R) (S : Subgroup R)
      let AZ : Subgroup R := A ⊔ Z
      have hZ_comm : IsMulCommutative Z := by
        refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
        apply Subtype.ext
        exact
          (Subgroup.mem_centralizer_iff.mp x.property.2
            (y : R) y.property.1).symm
      have hZ_le_cent_A : Z ≤ Subgroup.centralizer (A : Set R) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact Subgroup.mem_centralizer_iff.mp hz.2 a (hA.1 ha)
      have hA_le_cent_Z : A ≤ Subgroup.centralizer (Z : Set R) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp hz.2 a (hA.1 ha)).symm
      have hAZ_comm : IsMulCommutative AZ := by
        have hA_self : A ≤ Subgroup.centralizer (A : Set R) :=
          (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1
        have hZ_self : Z ≤ Subgroup.centralizer (Z : Set R) :=
          (Subgroup.le_centralizer_iff_isMulCommutative (K := Z)).2 hZ_comm
        exact (Subgroup.le_centralizer_iff_isMulCommutative (K := AZ)).1
          (Subgroup.le_centralizer_sup_of_le_centralizers
            (sup_le hA_self hZ_le_cent_A) (sup_le hA_le_cent_Z hZ_self))
      have hAZ_le_S : AZ ≤ (S : Subgroup R) :=
        sup_le hA.1 (by
          intro z hz
          exact hz.1)
      have hA_rank_le_AZ : generatorRank A ≤ generatorRank AZ := by
        have hAp : IsPGroup q A :=
          IsPGroup.to_le (H := A) (K := (S : Subgroup R))
            S.isPGroup' hA.1
        have hAZp : IsPGroup q AZ :=
          IsPGroup.to_le (H := AZ) (K := (S : Subgroup R))
            S.isPGroup' hAZ_le_S
        letI : Fact (IsPGroup q A) := ⟨hAp⟩
        letI : IsMulCommutative A := hA.2.1
        let A' : Subgroup AZ := A.subgroupOf AZ
        let eA : A' ≃* A :=
          Subgroup.subgroupOfEquivOfLe (H := A) (K := AZ) le_sup_left
        exact
          (generatorRank_le_groupRank_of_commutative_pgroup (p := q) A).trans
            ((groupRank_le_of_equiv eA).trans
              ((groupRank_le_of_subgroup A').trans
                (groupRank_le_generatorRank_of_commutative_pgroup
                  (p := q) hAZp hAZ_comm)))
      have hAZ_mem :
          AZ ∈ huppertRankThompsonAbelianSubgroups
            (G := R) (S : Subgroup R) := by
        refine ⟨hAZ_le_S, hAZ_comm, ?_⟩
        intro B hB_le hB_comm
        exact (hA.2.2 B hB_le hB_comm).trans hA_rank_le_AZ
      have hZ_le_AZ : Z ≤ AZ := by
        simp [AZ]
      have hAZ_le_Jrank : AZ ≤ Jrank := by
        change AZ ≤
          sSup (huppertRankThompsonAbelianSubgroups
            (G := R) (S : Subgroup R))
        exact le_sSup hAZ_mem
      have hZ_le_Jrank : Z ≤ Jrank :=
        hZ_le_AZ.trans hAZ_le_Jrank
      have hZ_ne_bot : Z ≠ ⊥ := by
        simpa [Z] using
          section8_centerIn_ne_bot_of_isPGroup S.isPGroup'
            (Sylow.ne_bot_of_dvd_card (G := R) (p := q) S hq_dvd)
      intro hJbot
      apply hZ_ne_bot
      exact le_bot_iff.mp (by simpa [hJbot] using hZ_le_Jrank)
    have hnormalizer_rank_ne_top : Nrank ≠ ⊤ := by
      intro htop
      have hJrank_normal : Jrank.Normal := by
        apply Subgroup.normalizer_eq_top_iff.mp
        simpa [Nrank] using htop
      have hJrank_p : IsPGroup q Jrank :=
        IsPGroup.to_le (H := Jrank) (K := (S : Subgroup R))
          S.isPGroup' hJrank_le_S
      have hJrank_le_pCore : Jrank ≤ pCore q R :=
        le_sSup ⟨hJrank_normal, hJrank_p⟩
      have hpCore_ne_bot : pCore q R ≠ ⊥ := by
        intro hcore_bot
        have hJrank_le_bot : Jrank ≤ (⊥ : Subgroup R) := by
          simpa [hcore_bot] using hJrank_le_pCore
        exact hJrank_ne_bot (le_bot_iff.mp hJrank_le_bot)
      rcases hchar_simple (pCore q R)
          (pCore_characteristic (G := R) (p := q)) with hcore_bot | hcore_top
      · exact hpCore_ne_bot hcore_bot
      · have htop_q : IsPGroup q (⊤ : Subgroup R) := by
          have hpcore_q : IsPGroup q (pCore q R) :=
            pCore_isPGroup (G := R) (p := q)
          rwa [hcore_top] at hpcore_q
        have hR_q : IsPGroup q R :=
          htop_q.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup R) ≃* R)
        haveI : Group.IsNilpotent R := hR_q.isNilpotent
        exact hnot_solvable IsNilpotent.to_isSolvable
    have hnormalizer_rank_ne_bot : Nrank ≠ ⊥ := by
      intro hNbot
      have hJrank_le_Nrank : Jrank ≤ Nrank := by
        simpa [Nrank] using
          (Subgroup.le_normalizer :
            Jrank ≤ Subgroup.normalizer (Jrank : Set R))
      have hJrank_bot : Jrank = ⊥ := by
        rw [hNbot] at hJrank_le_Nrank
        exact le_bot_iff.mp hJrank_le_Nrank
      have hnormalizer_bot :
          Subgroup.normalizer ((⊥ : Subgroup R) : Set R) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr
          (inferInstance : (⊥ : Subgroup R).Normal)
      exact hnormalizer_rank_ne_top (by
        simpa [Nrank, hJrank_bot] using hnormalizer_bot)
    have hJrankψ :
        ∀ x : R, x ∈ Jrank ↔ ψ x ∈ Jrank := by
      have hSψ_symm :
          ∀ x : R, x ∈ (S : Subgroup R) ↔
            ψ.symm x ∈ (S : Subgroup R) :=
        hkt_subgroup_invariant_symm ψ (S : Subgroup R) hSψ
      have hfamily_image :
          (MulEquiv.mapSubgroup ψ) ''
              huppertRankThompsonAbelianSubgroups
                (G := R) (S : Subgroup R) =
            huppertRankThompsonAbelianSubgroups
              (G := R) (S : Subgroup R) := by
        ext A
        constructor
        · rintro ⟨B, hB, rfl⟩
          refine ⟨?_, ?_, ?_⟩
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            exact (hSψ y).mp (hB.1 hy)
          · letI : IsMulCommutative B := hB.2.1
            exact Subgroup.map_isMulCommutative
              (H := B) ψ.toMonoidHom
          · intro C hC_le_S hC_comm
            have hCmap_le_S :
                C.map ψ.symm.toMonoidHom ≤ (S : Subgroup R) := by
              intro x hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
              exact (hSψ_symm y).mp (hC_le_S hy)
            have hCmap_comm :
                IsMulCommutative (C.map ψ.symm.toMonoidHom) := by
              letI : IsMulCommutative C := hC_comm
              exact Subgroup.map_isMulCommutative
                (H := C) ψ.symm.toMonoidHom
            have hBmax := hB.2.2
              (C.map ψ.symm.toMonoidHom) hCmap_le_S hCmap_comm
            calc
              generatorRank C =
                  generatorRank (C.map ψ.symm.toMonoidHom) := by
                    exact
                      (section9_c92_generatorRank_map_injective_eq
                        (A := C) ψ.symm.toMonoidHom ψ.symm.injective).symm
              _ ≤ generatorRank B := hBmax
              _ = generatorRank (B.map ψ.toMonoidHom) := by
                    exact
                      (section9_c92_generatorRank_map_injective_eq
                        (A := B) ψ.toMonoidHom ψ.injective).symm
        · intro hA
          refine ⟨A.map ψ.symm.toMonoidHom, ?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · intro x hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
              exact (hSψ_symm y).mp (hA.1 hy)
            · letI : IsMulCommutative A := hA.2.1
              exact Subgroup.map_isMulCommutative
                (H := A) ψ.symm.toMonoidHom
            · intro C hC_le_S hC_comm
              have hCmap_le_S :
                  C.map ψ.toMonoidHom ≤ (S : Subgroup R) := by
                intro x hx
                rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                exact (hSψ y).mp (hC_le_S hy)
              have hCmap_comm :
                  IsMulCommutative (C.map ψ.toMonoidHom) := by
                letI : IsMulCommutative C := hC_comm
                exact Subgroup.map_isMulCommutative
                  (H := C) ψ.toMonoidHom
              have hAmax := hA.2.2
                (C.map ψ.toMonoidHom) hCmap_le_S hCmap_comm
              calc
                generatorRank C =
                    generatorRank (C.map ψ.toMonoidHom) := by
                      exact
                        (section9_c92_generatorRank_map_injective_eq
                          (A := C) ψ.toMonoidHom ψ.injective).symm
                _ ≤ generatorRank A := hAmax
                _ = generatorRank (A.map ψ.symm.toMonoidHom) := by
                      exact
                        (section9_c92_generatorRank_map_injective_eq
                          (A := A) ψ.symm.toMonoidHom ψ.symm.injective).symm
          · ext x
            simp
      have hJrank_map : Jrank.map ψ.toMonoidHom = Jrank := by
        calc
          Jrank.map ψ.toMonoidHom =
              (MulEquiv.mapSubgroup ψ)
                (sSup (huppertRankThompsonAbelianSubgroups
                  (G := R) (S : Subgroup R))) := by rfl
          _ = sSup ((MulEquiv.mapSubgroup ψ) ''
                huppertRankThompsonAbelianSubgroups
                  (G := R) (S : Subgroup R)) := by simp
          _ = Jrank := by
            simpa [Jrank, huppertRankThompsonSubgroup] using
              congrArg sSup hfamily_image
      intro x
      constructor
      · intro hx
        have hxmap : ψ x ∈ Jrank.map ψ.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hJrank_map] at hxmap
        exact hxmap
      · intro hx
        have hxmap : ψ x ∈ Jrank.map ψ.toMonoidHom := by
          rw [hJrank_map]
          exact hx
        rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
        have hy_eq : y = x := ψ.injective hyx
        simpa [hy_eq] using hy
    have hnormalizer_rankψ :
        ∀ x : R, x ∈ Nrank ↔ ψ x ∈ Nrank := by
      simpa [Nrank] using
        hkt_normalizer_invariant_of_invariant ψ Jrank hJrankψ
    have hnormalizer_rank :
        HasNormalPComplement q Nrank :=
      hkt_hasNormalPComplement_of_proper_invariant_subgroup_induction
        (Q := R) (φ := ψ) (p := q) Nrank
        hproper_invariant_subgroup_nil hnormalizer_rank_ne_bot
        hnormalizer_rank_ne_top hnormalizer_rankψ
    have hcentralizer_ne_bot : C ≠ ⊥ := by
      have hS_ne_bot : (S : Subgroup R) ≠ ⊥ :=
        Sylow.ne_bot_of_dvd_card (G := R) (p := q) S hq_dvd
      have hZ_ne_bot : centerIn (G := R) (S : Subgroup R) ≠ ⊥ :=
        section8_centerIn_ne_bot_of_isPGroup S.isPGroup' hS_ne_bot
      have hZ_le_C :
          centerIn (G := R) (S : Subgroup R) ≤
            Subgroup.centralizer (centerIn (G := R) (S : Subgroup R) : Set R) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hz_cent : z ∈ Subgroup.centralizer ((S : Subgroup R) : Set R) := by
          simpa [centerIn] using hz.2
        exact Subgroup.mem_centralizer_iff.mp hz_cent y hy.1
      intro hCbot
      have hZ_le_bot : centerIn (G := R) (S : Subgroup R) ≤ (⊥ : Subgroup R) := by
        rw [← hCbot]
        simpa [C] using hZ_le_C
      exact hZ_ne_bot (le_bot_iff.mp hZ_le_bot)
    have hcentralizer_ne_top : C ≠ ⊤ := by
      simpa [C] using
        hkt_centralizer_center_sylow_ne_top_of_center_eq_bot
          S hq_dvd hcenter_bot
    have hcentralizerψ : ∀ x : R, x ∈ C ↔ ψ x ∈ C := by
      have hZψ :
          ∀ x : R,
            x ∈ centerIn (G := R) (S : Subgroup R) ↔
              ψ x ∈ centerIn (G := R) (S : Subgroup R) :=
        hkt_centerIn_sylow_invariant_of_invariant_sylow ψ S hSψ
      simpa [C] using hkt_centralizer_invariant_of_invariant ψ
        (centerIn (G := R) (S : Subgroup R)) hZψ
    have hcomp : HasNormalPComplement q R :=
      hkt_has_normal_p_complement_of_invariant_odd_sylow
        ψ hq2 S hproper_invariant_subgroup_nil
        (by simpa [Nrank] using hnormalizer_rank)
        (by simpa [N] using hnormalizer_ne_bot)
        (by simpa [N] using hnormalizer_ne_top)
        (by simpa [N] using hnormalizerψ)
        (by simpa [C] using hcentralizer_ne_bot)
        (by simpa [C] using hcentralizer_ne_top)
        (by simpa [C] using hcentralizerψ)
    exact hkt_false_of_normal_p_complement_in_minimal_branch
      ψ hnot_solvable hproper_invariant_subgroup_nil
      hproper_invariant_quotient_nil hq_dvd hcomp
  exact hP (Nat.card Q) Q φ rfl hperiod hprod hnot_two

/--
The `p = 2` branch of Huppert V.8.13: the product identity forces the
automorphism to be inversion, hence the group is commutative and nilpotent.
-/
private theorem hkt_nilpotent_of_period_two_product_identity
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (hprod :
      ∀ q : Q,
        ((List.range 2).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    Group.IsNilpotent Q := by
  classical
  have hmul : ∀ q : Q, q * φ q = 1 := by
    intro q
    simpa using hprod q
  have hφ_inv : ∀ q : Q, φ q = q⁻¹ := by
    intro q
    exact eq_inv_of_mul_eq_one_right (hmul q)
  have hcomm : ∀ x y : Q, x * y = y * x := by
    intro x y
    have hxy : φ (x * y) = (x * y)⁻¹ := hφ_inv (x * y)
    have hxy' : φ (x * y) = x⁻¹ * y⁻¹ := by
      calc
        φ (x * y) = φ x * φ y := by simp
        _ = x⁻¹ * y⁻¹ := by rw [hφ_inv x, hφ_inv y]
    have hinv_eq : (x * y)⁻¹ = x⁻¹ * y⁻¹ := hxy.symm.trans hxy'
    have hswap_inv : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := by
      simpa [mul_inv_rev] using hinv_eq
    apply inv_injective
    simpa [mul_inv_rev] using hswap_inv
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  infer_instance

/--
The remaining odd-prime branch of Huppert V.8.13 after the elementary `p = 2`
case has been closed. This is the current HKT minimal-counterexample core.
-/
private theorem hkt_nilpotent_of_odd_prime_period_product_identity
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    Group.IsNilpotent Q := by
  by_cases htwo : IsPGroup 2 Q
  · exact htwo.isNilpotent
  · exact hkt_nilpotent_of_odd_prime_period_product_identity_not_two_group
      φ hprime hp2 hperiod hprod htwo

/--
Huppert V.8.13 / Hughes--Kegel--Thompson core used by Thompson V.8.14:
a finite group with a prime-period automorphism satisfying the fixed-point-free
product identity is nilpotent. The `p = 2` branch is formalized directly;
the remaining proof debt is the named odd-prime minimal-counterexample core.
-/
private theorem hkt_nilpotent_of_prime_period_product_identity
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (hprime : Nat.Prime p)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    Group.IsNilpotent Q := by
  by_cases hp2 : p = 2
  · subst p
    exact hkt_nilpotent_of_period_two_product_identity φ hprod
  · exact hkt_nilpotent_of_odd_prime_period_product_identity φ hprime hp2 hperiod hprod

/--
Smallest explicit reduction for the Thompson prime-order theorem: extract the
fixed-point-free product identity and isolate the remaining Huppert V.8.13
step as a separate helper.
-/
private theorem thompson_prime_order_fixedPointFree_hkt_reduction
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (hprime : Nat.Prime (orderOf φ))
    (hfixed : ∀ q : Q, φ q = q → q = 1) :
    Group.IsNilpotent Q := by
  classical
  have hFPF : MonoidHom.FixedPointFree (fun q : Q => φ q) := by
    intro q hq
    exact hfixed q hq
  have hpow_apply : ∀ n q, (φ ^ n) q = (fun q : Q => φ q)^[n] q := by
    intro n
    induction n with
    | zero => intro q; simp
    | succ n ih =>
        intro q
        simp [pow_succ, Function.iterate_succ, ih]
  have hperiod : (fun q : Q => φ q)^[orderOf φ] = id := by
    ext q
    have hpow : (φ ^ orderOf φ : MulAut Q) = 1 := pow_orderOf_eq_one φ
    have hq := congrArg (fun g : MulAut Q => g q) hpow
    change (φ ^ orderOf φ) q = q at hq
    rw [hpow_apply] at hq
    simpa using hq
  have hprod :
      ∀ q : Q,
        ((List.range (orderOf φ)).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1 := by
    intro q
    exact MonoidHom.FixedPointFree.prod_pow_eq_one hFPF hperiod q
  exact hkt_nilpotent_of_prime_period_product_identity φ hprime hperiod hprod

/--
Thompson's fixed-point-free automorphism theorem, in the prime-order form:
if a finite group admits a fixed-point-free automorphism of prime order, then
the group is nilpotent.
-/
public theorem thompson_prime_order_fixedPointFree_automorphism_nilpotent
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (hprime : Nat.Prime (orderOf φ))
    (hfixed : ∀ q : Q, φ q = q → q = 1) :
    Group.IsNilpotent Q := by
  exact thompson_prime_order_fixedPointFree_hkt_reduction φ hprime hfixed

/--
The subgroup-of-automorphisms version used after extracting a prime-order
element from a nontrivial fixed-point-free automorphism group.
-/
public theorem thompson_fixedPointFree_automorphism_subgroup_nilpotent
    {Q : Type u} [Group Q] [Finite Q] (A : Subgroup (MulAut Q))
    (hA_nontrivial : ∃ φ : A, φ ≠ 1)
    (hfixed : ∀ φ : A, φ ≠ 1 → ∀ q : Q, (φ : MulAut Q) q = q → q = 1) :
    Group.IsNilpotent Q := by
  classical
  haveI : Finite A := inferInstance
  by_cases hcard : Nat.card A = 1
  · have hsub : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hcard).1
    rcases hA_nontrivial with ⟨φ, hφ⟩
    exact False.elim (hφ (Subsingleton.elim φ 1))
  · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    obtain ⟨φ, hφorder⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpdvd
    have hφneA : φ ≠ 1 := by
      intro hφeq
      have hp_one : p = 1 := by
        simpa [hφeq] using hφorder.symm
      exact hp.ne_one hp_one
    have hφfixed : ∀ q : Q, (φ : MulAut Q) q = q → q = 1 := by
      intro q hq
      exact hfixed φ hφneA q hq
    have hprime : Nat.Prime (orderOf (φ : MulAut Q)) := by
      have horder : orderOf (φ : MulAut Q) = p := by
        simpa [Subgroup.orderOf_coe] using hφorder
      simpa [horder] using hp
    exact
      thompson_prime_order_fixedPointFree_automorphism_nilpotent
        (Q := Q) (φ := (φ : MulAut Q)) hprime hφfixed

/--
Peterfalvi-shaped conjugation version: a nontrivial subgroup `K` normalizes a
finite subgroup `Q`, and every nonidentity element of `K` centralizes only the
identity element of `Q`; hence `Q` is nilpotent.
-/
public theorem thompson_fixedPointFree_conjugation_nilpotent_subgroup
    {G : Type u} [Group G] [Finite G] (Q K : Subgroup G)
    (hK_norm_Q : K ≤ Subgroup.normalizer Q)
    (hK_nontrivial : ∃ x : G, x ∈ K ∧ x ≠ 1)
    (hfixed : ∀ x : G, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ Q = ⊥) :
    Group.IsNilpotent Q := by
  classical
  by_cases hQsub : Subsingleton Q
  · exact Group.isNilpotent_of_subsingleton
  let conjHom : K →* MulAut Q :=
    Q.normalizerMonoidHom.comp (Subgroup.inclusion hK_norm_Q)
  let A : Subgroup (MulAut Q) := Subgroup.map conjHom ⊤
  have hA_nontrivial : ∃ φ : A, φ ≠ 1 := by
    rcases hK_nontrivial with ⟨x, hxK, hxne⟩
    let xK : K := ⟨x, hxK⟩
    have hxconj_ne : conjHom xK ≠ 1 := by
      intro hxconj
      have hsub : Subsingleton Q := by
        refine ⟨fun q r => ?_⟩
        have h_eq_one : ∀ q : Q, q = 1 := by
          intro q
          have hcomm : x * (q : G) = (q : G) * x := by
            have hfixq : conjHom xK q = q := by
              simp [hxconj]
            have hcoe : (x : G) * (q : G) * x⁻¹ = (q : G) := by
              simpa [conjHom, xK] using congrArg (fun z : Q => (z : G)) hfixq
            calc
              x * (q : G) = (x * (q : G) * x⁻¹) * x := by simp [mul_assoc]
              _ = (q : G) * x := by rw [hcoe]
          have hmemCentral :
              (q : G) ∈ Subgroup.centralizer ({x} : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff.mp hy]
            exact hcomm
          have hmemInf :
              (q : G) ∈ Subgroup.centralizer ({x} : Set G) ⊓ Q :=
            ⟨hmemCentral, q.2⟩
          have hbot : (q : G) ∈ (⊥ : Subgroup G) := by
            simpa [hfixed x hxK hxne] using hmemInf
          exact Subtype.ext (by simpa using hbot)
        exact (h_eq_one q).trans (h_eq_one r).symm
      exact hQsub hsub
    refine ⟨⟨conjHom xK, ?_⟩, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨xK, by simp, rfl⟩
    · intro hφ
      exact hxconj_ne (Subtype.ext_iff.mp hφ)
  have hA_fixed :
      ∀ φ : A, φ ≠ 1 → ∀ q : Q, (φ : MulAut Q) q = q → q = 1 := by
    intro φ hφne q hφq
    rcases Subgroup.mem_map.mp φ.2 with ⟨xK, _hxTop, hxφ⟩
    have hxne : (xK : G) ≠ 1 := by
      intro hxone
      have hφone_val : (φ : MulAut Q) = 1 := by
        rw [← hxφ]
        ext q
        simp [conjHom, hxone]
      exact hφne (Subtype.ext hφone_val)
    have hcomm : (xK : G) * (q : G) = (q : G) * (xK : G) := by
      have hfixq : conjHom xK q = q := by
        simpa [hxφ] using hφq
      have hcoe : (xK : G) * (q : G) * (xK : G)⁻¹ = (q : G) := by
        simpa [conjHom] using congrArg (fun z : Q => (z : G)) hfixq
      calc
        (xK : G) * (q : G) =
            ((xK : G) * (q : G) * (xK : G)⁻¹) * (xK : G) := by
          simp [mul_assoc]
        _ = (q : G) * (xK : G) := by rw [hcoe]
    have hmemCentral :
        (q : G) ∈ Subgroup.centralizer ({(xK : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hcomm
    have hmemInf :
        (q : G) ∈ Subgroup.centralizer ({(xK : G)} : Set G) ⊓ Q :=
      ⟨hmemCentral, q.2⟩
    have hbot : (q : G) ∈ (⊥ : Subgroup G) := by
      simpa [hfixed (xK : G) xK.2 hxne] using hmemInf
    exact Subtype.ext (by simpa using hbot)
  exact thompson_fixedPointFree_automorphism_subgroup_nilpotent A hA_nontrivial hA_fixed


/-- Huppert V.8.14, Peterfalvi/Suzuki-shaped conjugation interface. -/
public theorem huppert_V_8_14_thompson_fixedPointFree_conjugation_nilpotent_subgroup
    {G : Type u} [Group G] [Finite G] (Q K : Subgroup G)
    (hK_norm_Q : K ≤ Subgroup.normalizer Q)
    (hK_nontrivial : ∃ x : G, x ∈ K ∧ x ≠ 1)
    (hfixed : ∀ x : G, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ Q = ⊥) :
    Group.IsNilpotent Q :=
  thompson_fixedPointFree_conjugation_nilpotent_subgroup
    (G := G) Q K hK_norm_Q hK_nontrivial hfixed

end External
end CFSG.BenderSuzuki
