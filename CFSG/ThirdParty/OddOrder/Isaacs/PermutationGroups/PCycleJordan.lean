/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.CycleCommutators

/-!
# Isaacs, Finite Group Theory — Ch. 8: the `p`-cycle Jordan theorem (Thm 8.23)

Formalizes **Isaacs Thm 8.23** (pp. 236–237; Wielandt 13.9): a primitive
subgroup `G ≤ Sym(Ω)` containing a `p`-cycle with `p` prime and
`p ≤ |Ω| - 3` contains the alternating group
(`alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`).  This is mathlib's
`proof_wanted alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`
(`Mathlib.GroupTheory.GroupAction.Jordan`).

Proof structure (following Isaacs, with the quotient arguments replaced by
element-level corrections):

* agreement-transport lemmas: permutations agreeing on an invariant set
  have agreeing inverses, products, commutators and powers;
* `exists_agree_of_isMultiplyPretransitive`: an `|S|`-transitive subgroup
  of `Perm α` realizes any prescribed permutation on `S` — applicable since
  Jordan's criterion (`IsPreprimitive.isMultiplyPreprimitive`) makes `G`
  highly transitive on the fixed points `Λ = supportᶜ` of the `p`-cycle `g`;
* `card_inf_fixing_dvd_factorial`: the pointwise stabilizer
  `F = G ⊓ fix(Λ)` embeds in `Perm (support g)`, so `|F| ∣ p!` and `⟨g⟩` is
  a full Sylow `p`-subgroup of `F`;
* `exists_mul_mem_normalizer_zpowers`: Sylow conjugation inside `F` corrects
  a realizing element to one normalizing `⟨g⟩` (Isaacs's Frattini argument);
* `commute_commutator_of_mem_normalizer`: `Aut ⟨g⟩` is abelian, so the
  commutator `x` of two corrected realizations centralizes `g`;
* main assembly: `x` agrees on `Λ` with the commutator `t` of two swaps,
  a `3`-cycle by Lem 8.25; `x` commutes with `g`, so by
  `IsCycle.commute_iff` its restriction to the support is a power of `g`
  and `x ^ p` fixes the support pointwise; hence `x ^ p = t ^ p`, again a
  `3`-cycle since `3 ∤ p`, and the `3`-cycle Jordan theorem applies.
  (`p = 3` is the `3`-cycle Jordan theorem directly.)
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open Equiv Equiv.Perm MulAction

open scoped commutatorElement

variable {α : Type*}

/-! ### Agreement transport on an invariant set -/

section Agree

variable {x w x₁ x₂ w₁ w₂ : Perm α} {S : Set α}

/-- Invariance of a set under `w` transfers to `w⁻¹`. -/
private lemma inv_invariant (hwS : ∀ b, b ∈ S ↔ w b ∈ S) (b : α) :
    b ∈ S ↔ w⁻¹ b ∈ S := by
  constructor
  · intro hb
    exact (hwS (w⁻¹ b)).mpr (by simpa using hb)
  · intro hb
    have := (hwS (w⁻¹ b)).mp hb
    simpa using this

/-- Two permutations agreeing on a `w`-invariant set have agreeing
inverses there. -/
private lemma inv_apply_eq_of_agree (hwS : ∀ b, b ∈ S ↔ w b ∈ S)
    (h : ∀ b ∈ S, x b = w b) : ∀ b ∈ S, x⁻¹ b = w⁻¹ b := by
  intro b hb
  have hw : w⁻¹ b ∈ S := (inv_invariant hwS b).mp hb
  have hx : x (w⁻¹ b) = b := (h _ hw).trans (by simp)
  apply x.injective
  rw [hx]
  simp

/-- Agreement on an invariant set is preserved by products. -/
private lemma mul_apply_eq_of_agree (h₂S : ∀ b, b ∈ S ↔ w₂ b ∈ S)
    (h₁ : ∀ b ∈ S, x₁ b = w₁ b) (h₂ : ∀ b ∈ S, x₂ b = w₂ b) :
    ∀ b ∈ S, (x₁ * x₂) b = (w₁ * w₂) b := by
  intro b hb
  rw [Perm.mul_apply, Perm.mul_apply, h₂ b hb]
  exact h₁ _ ((h₂S b).mp hb)

/-- Agreement on an invariant set is preserved by commutators. -/
private lemma commutator_apply_eq_of_agree
    (h₁S : ∀ b, b ∈ S ↔ w₁ b ∈ S) (h₂S : ∀ b, b ∈ S ↔ w₂ b ∈ S)
    (h₁ : ∀ b ∈ S, x₁ b = w₁ b) (h₂ : ∀ b ∈ S, x₂ b = w₂ b) :
    ∀ b ∈ S, ⁅x₁, x₂⁆ b = ⁅w₁, w₂⁆ b := by
  intro b hb
  rw [commutatorElement_def, commutatorElement_def]
  exact mul_apply_eq_of_agree (inv_invariant h₂S)
    (mul_apply_eq_of_agree (inv_invariant h₁S)
      (mul_apply_eq_of_agree h₂S h₁ h₂)
      (inv_apply_eq_of_agree h₁S h₁))
    (inv_apply_eq_of_agree h₂S h₂) b hb

/-- Agreement on an invariant set is preserved by powers. -/
private lemma pow_apply_eq_of_agree (hwS : ∀ b, b ∈ S ↔ w b ∈ S)
    (h : ∀ b ∈ S, x b = w b) (n : ℕ) :
    ∀ b ∈ S, (x ^ n) b = (w ^ n) b := by
  induction n with
  | zero => intro b _; simp
  | succ n ih =>
    intro b hb
    rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply, h b hb]
    exact ih _ ((hwS b).mp hb)

end Agree

/-! ### Realizing prescribed behavior by multiple transitivity -/

/-- A subgroup of `Perm α` that is `|S|`-transitive contains an element
agreeing with any prescribed permutation on the finset `S`. -/
private lemma exists_agree_of_isMultiplyPretransitive
    {G : Subgroup (Perm α)} {S : Finset α}
    (hT : IsMultiplyPretransitive G α S.card) (τ : Perm α) :
    ∃ k : Perm α, k ∈ G ∧ ∀ b ∈ S, k b = τ b := by
  classical
  have := hT
  set e : Fin S.card ≃ {b // b ∈ S} := S.equivFin.symm with he
  set ι₁ : Fin S.card ↪ α :=
    ⟨fun i => ↑(e i), fun i j hij => e.injective (Subtype.ext hij)⟩ with hι₁
  set ι₂ : Fin S.card ↪ α :=
    ⟨fun i => τ ↑(e i), fun i j hij =>
      e.injective (Subtype.ext (τ.injective hij))⟩ with hι₂
  obtain ⟨k, hk⟩ := exists_smul_eq (M := G) ι₁ ι₂
  refine ⟨(k : Perm α), k.2, fun b hb => ?_⟩
  have happ : (k • ι₁) (e.symm ⟨b, hb⟩) = ι₂ (e.symm ⟨b, hb⟩) := by rw [hk]
  rw [Function.Embedding.smul_apply] at happ
  have hb1 : ι₁ (e.symm ⟨b, hb⟩) = b := by
    rw [hι₁]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
  have hb2 : ι₂ (e.symm ⟨b, hb⟩) = τ b := by
    rw [hι₂]
    exact congrArg τ (congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩))
  rw [hb1, hb2] at happ
  exact happ

/-! ### The pointwise stabilizer of the fixed points of `g` -/

section FixingSubgroup

variable [DecidableEq α] [Fintype α]

/-- A permutation fixing the complement of `g.support` pointwise preserves
`g.support`. -/
private lemma mem_support_iff_of_fixes_compl {g σ : Perm α}
    (hσ : ∀ b ∉ g.support, σ b = b) (b : α) :
    b ∈ g.support ↔ σ b ∈ g.support := by
  constructor
  · intro hb
    by_contra hc
    have h2 : σ b = b := σ.injective (hσ _ hc)
    exact hc (h2.symm ▸ hb)
  · intro hb
    by_contra hc
    exact hc (hσ b hc ▸ hb)

/-- Elements of `G ⊓ fixingSubgroup (supportᶜ)` fix the complement of the
support pointwise. -/
private lemma fixes_compl_of_mem_inf_fixing {G : Subgroup (Perm α)} {g : Perm α}
    {σ : Perm α} (hσ : σ ∈ G ⊓ fixingSubgroup (Perm α) ((↑g.supportᶜ : Set α)))
    (b : α) (hb : b ∉ g.support) : σ b = b := by
  have h2 := (Subgroup.mem_inf.mp hσ).2
  rw [mem_fixingSubgroup_iff] at h2
  exact h2 b (by simpa using hb)

/-- **Isaacs Thm 8.23, step (Sylow bound)** — the pointwise stabilizer
`F = G ⊓ fix(supportᶜ)` acts faithfully on the support, so its order
divides `|support g|!`. -/
private lemma card_inf_fixing_dvd_factorial (G : Subgroup (Perm α)) (g : Perm α) :
    Nat.card ↥(G ⊓ fixingSubgroup (Perm α) ((↑g.supportᶜ : Set α)))
      ∣ Nat.factorial g.support.card := by
  classical
  set F := G ⊓ fixingSubgroup (Perm α) ((↑g.supportᶜ : Set α)) with hFdef
  set Φ : ↥F →* Perm {b // b ∈ g.support} := MonoidHom.mk'
    (fun σ => (σ : Perm α).subtypePerm fun b =>
      (mem_support_iff_of_fixes_compl (fixes_compl_of_mem_inf_fixing σ.2) b).symm)
    (fun σ₁ σ₂ => by ext b; rfl) with hΦdef
  have hinj : Function.Injective Φ := by
    intro σ₁ σ₂ h
    ext b
    by_cases hb : b ∈ g.support
    · have h2 := congrArg (fun π : Perm {b // b ∈ g.support} => (π ⟨b, hb⟩ : α)) h
      exact h2
    · rw [fixes_compl_of_mem_inf_fixing σ₁.2 b hb,
        fixes_compl_of_mem_inf_fixing σ₂.2 b hb]
  calc Nat.card ↥F
      = Nat.card Φ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    _ ∣ Nat.card (Perm {b // b ∈ g.support}) :=
        Subgroup.card_subgroup_dvd_card _
    _ = Nat.factorial g.support.card := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]

end FixingSubgroup

/-! ### Sylow conjugation and the abelian-automorphism centralizer step -/

section SylowConj

open scoped Pointwise

variable {M : Type*} [Group M] [Finite M]

/-- **Isaacs Thm 8.23, Frattini correction** — if `F` contains an element
`g` of prime order `p` and `|F| ∣ p!`, then `⟨g⟩` is a full Sylow
`p`-subgroup of `F`, so any `k` conjugating `F` into itself can be corrected
by an element `h ∈ F` so that `h * k` normalizes `⟨g⟩`. -/
private lemma exists_mul_mem_normalizer_zpowers {p : ℕ} (hp : p.Prime)
    {F : Subgroup M} {g : M} (hgF : g ∈ F) (hord : orderOf g = p)
    (hcard : Nat.card F ∣ Nat.factorial p)
    {k : M} (hk : ∀ q ∈ F, k * q * k⁻¹ ∈ F) :
    ∃ h ∈ F, h * k ∈ Subgroup.normalizer (Subgroup.zpowers g) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcard0 : Nat.card F ≠ 0 := Nat.card_pos.ne'
  -- `p` divides `|F|` exactly once
  have hordF : orderOf (⟨g, hgF⟩ : F) = p :=
    (orderOf_injective F.subtype F.subtype_injective ⟨g, hgF⟩).symm.trans hord
  have hpF : p ∣ Nat.card F := hordF ▸ orderOf_dvd_natCard (⟨g, hgF⟩ : F)
  have hp2F : ¬ p * p ∣ Nat.card F := by
    intro hc
    have h1 : p * p ∣ Nat.factorial p := hc.trans hcard
    have h2 : Nat.factorial p = p * Nat.factorial (p - 1) :=
      (Nat.mul_factorial_pred hp.pos.ne').symm
    rw [h2] at h1
    have h3 : p ∣ Nat.factorial (p - 1) :=
      (Nat.mul_dvd_mul_iff_left hp.pos).mp h1
    have h4 := (Nat.Prime.dvd_factorial hp).mp h3
    have h5 := hp.pos
    omega
  have hfact : (Nat.card F).factorization p = 1 := by
    have h1 : 1 ≤ (Nat.card F).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hcard0).mp (by simpa using hpF)
    have h2 : ¬ 2 ≤ (Nat.card F).factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hcard0]
      simpa [pow_two] using hp2F
    omega
  -- the two conjugate order-`p` subgroups, as Sylow subgroups of `F`
  have hPle : Subgroup.zpowers g ≤ F := Subgroup.zpowers_le.mpr hgF
  have hgF' : k * g * k⁻¹ ∈ F := hk g hgF
  have hordg' : orderOf (k * g * k⁻¹) = p := by
    have h1 := orderOf_injective (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective g
    simpa [MulAut.conj_apply, hord] using h1
  have hQle : Subgroup.zpowers (k * g * k⁻¹) ≤ F := Subgroup.zpowers_le.mpr hgF'
  have hcardP : Nat.card ((Subgroup.zpowers g).subgroupOf F) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv,
      Nat.card_zpowers, hord]
  have hcardQ : Nat.card ((Subgroup.zpowers (k * g * k⁻¹)).subgroupOf F) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv,
      Nat.card_zpowers, hordg']
  set SP : Sylow p ↥F := Sylow.ofCard _ (by rw [hcardP, hfact, pow_one])
    with hSP
  set SQ : Sylow p ↥F := Sylow.ofCard _ (by rw [hcardQ, hfact, pow_one])
    with hSQ
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (M := ↥F) SQ SP
  have hsub : MulAut.conj h • (SQ : Subgroup ↥F) = (SP : Subgroup ↥F) := by
    rw [← Sylow.coe_subgroup_smul, hh]
  have hSPcoe : (SP : Subgroup ↥F) = (Subgroup.zpowers g).subgroupOf F := by
    rw [hSP, Sylow.coe_ofCard]
  have hSQcoe : (SQ : Subgroup ↥F) =
      (Subgroup.zpowers (k * g * k⁻¹)).subgroupOf F := by
    rw [hSQ, Sylow.coe_ofCard]
  refine ⟨↑h, h.2, Subgroup.mem_normalizer_iff.mpr fun w => ?_⟩
  constructor
  · -- `w ∈ ⟨g⟩ → (h k) w (h k)⁻¹ ∈ ⟨g⟩`
    intro hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hkw : k * w * k⁻¹ ∈ Subgroup.zpowers (k * g * k⁻¹) := by
      rw [← hn, ← conj_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
    have hkwF : k * w * k⁻¹ ∈ F := hk w (hPle hw)
    have hu : (⟨k * w * k⁻¹, hkwF⟩ : ↥F) ∈ (SQ : Subgroup ↥F) := by
      rw [hSQcoe]
      exact Subgroup.mem_subgroupOf.mpr hkw
    have hv : MulAut.conj h • (⟨k * w * k⁻¹, hkwF⟩ : ↥F) ∈ (SP : Subgroup ↥F) := by
      rw [← hsub]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hu
    rw [hSPcoe] at hv
    have hv' := Subgroup.mem_subgroupOf.mp hv
    have hval : ((MulAut.conj h • (⟨k * w * k⁻¹, hkwF⟩ : ↥F) : ↥F) : M) =
        ↑h * (k * w * k⁻¹) * (↑h)⁻¹ := rfl
    rw [hval] at hv'
    have hrw : ↑h * k * w * (↑h * k)⁻¹ = ↑h * (k * w * k⁻¹) * (↑h)⁻¹ := by
      group
    rwa [hrw]
  · -- `(h k) w (h k)⁻¹ ∈ ⟨g⟩ → w ∈ ⟨g⟩`
    intro hw
    have hwF : ↑h * k * w * (↑h * k)⁻¹ ∈ F := hPle hw
    have hv : (⟨↑h * k * w * (↑h * k)⁻¹, hwF⟩ : ↥F) ∈ (SP : Subgroup ↥F) := by
      rw [hSPcoe]
      exact Subgroup.mem_subgroupOf.mpr hw
    have hu : (MulAut.conj h)⁻¹ • (⟨↑h * k * w * (↑h * k)⁻¹, hwF⟩ : ↥F) ∈
        (SQ : Subgroup ↥F) := by
      rw [← Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsub]
      exact hv
    rw [hSQcoe] at hu
    have hu' := Subgroup.mem_subgroupOf.mp hu
    have hval : (((MulAut.conj h)⁻¹ • (⟨↑h * k * w * (↑h * k)⁻¹, hwF⟩ : ↥F) : ↥F) : M) =
        (↑h)⁻¹ * (↑h * k * w * (↑h * k)⁻¹) * ↑h := rfl
    rw [hval] at hu'
    have hrw : (↑h : M)⁻¹ * (↑h * k * w * (↑h * k)⁻¹) * ↑h = k * w * k⁻¹ := by
      group
    rw [hrw] at hu'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu'
    rw [conj_zpow] at hn
    have : g ^ n = w := by
      have := mul_left_cancel (a := k) (mul_right_cancel (b := k⁻¹) hn)
      exact this
    exact this ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) n

omit [Finite M] in
/-- **Isaacs Thm 8.23, centralizer step** — the automorphism group of the
cyclic group `⟨g⟩` is abelian, so the commutator of two elements
normalizing `⟨g⟩` centralizes it. -/
private lemma commute_commutator_of_mem_normalizer {g x₁ x₂ : M}
    (h₁ : x₁ ∈ Subgroup.normalizer (Subgroup.zpowers g : Set M))
    (h₂ : x₂ ∈ Subgroup.normalizer (Subgroup.zpowers g : Set M)) :
    Commute ⁅x₁, x₂⁆ g := by
  classical
  have : IsCyclic ↥(Subgroup.zpowers g) := by
    refine ⟨⟨⟨g, Subgroup.mem_zpowers g⟩, fun w => ?_⟩⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  set φ := (Subgroup.zpowers g).normalizerMonoidHom with hφ
  set c : ↥(Subgroup.normalizer (Subgroup.zpowers g : Set M)) :=
    ⁅(⟨x₁, h₁⟩ : ↥(Subgroup.normalizer (Subgroup.zpowers g : Set M))),
      ⟨x₂, h₂⟩⁆ with hc
  have hker : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    apply (IsCyclic.mulAutMulEquiv _).injective
    rw [map_mul, map_mul, mul_comm]
  rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  have hval : (c : M) = ⁅x₁, x₂⁆ := rfl
  rw [hval] at hker
  exact (Subgroup.mem_centralizer_iff.mp hker g (Subgroup.mem_zpowers g)).symm

end SylowConj

/-! ### Isaacs Thm 8.23 -/

section Main

variable [DecidableEq α] [Fintype α] {G : Subgroup (Perm α)}

/-- **Isaacs Thm 8.23** (Wielandt 13.9) — a primitive subgroup of `Perm α`
containing a cycle of prime order `p ≤ |α| - 3` contains the alternating
group.  This is mathlib's `proof_wanted
alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`. -/
theorem alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    (hG : IsPreprimitive G α)
    {p : ℕ} (hp : p.Prime) (hp' : p + 3 ≤ Nat.card α)
    {g : Perm α} (hgc : g.IsCycle) (hgp : g.support.card = p)
    (hg : g ∈ G) : alternatingGroup α ≤ G := by
  classical
  rcases eq_or_ne p 3 with rfl | hp3
  · -- `p = 3`: `g` is itself a three-cycle
    exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG
      (card_support_eq_three_iff.mp hgp) hg
  -- main case `p ≠ 3`
  have h2p := hp.two_le
  have hcardα : p + 3 ≤ Nat.card α := hp'
  obtain ⟨n, hn⟩ : ∃ n, Nat.card α - p = n + 1 :=
    ⟨Nat.card α - p - 1, by omega⟩
  -- (a) `G` is `|supportᶜ|`-transitive
  have hMPP : IsMultiplyPreprimitive G α (n + 2) := by
    apply hG.isMultiplyPreprimitive (s := (g.supportᶜ : Set α))
    · apply Nat.add_left_cancel
      rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset, hgp]
      omega
    · omega
    · have := isPretransitive_of_isCycle_mem hgc hg
      apply IsPreprimitive.of_prime_card
      suffices hcard :
          Nat.card (SubMulAction.ofFixingSubgroup G ((g.support : Set α)ᶜ)) = p by
        rw [hcard]; exact hp
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hgp]
      apply congr_arg
      ext b
      simp [SubMulAction.mem_ofFixingSubgroup_iff]
  have hMT : IsMultiplyPretransitive G α (g.supportᶜ : Finset α).card := by
    have := hMPP.isMultiplyPretransitive
    have hcc : (g.supportᶜ : Finset α).card = n + 1 := by
      rw [Finset.card_compl, hgp, ← Nat.card_eq_fintype_card]
      omega
    rw [hcc]
    exact isMultiplyPretransitive_of_le (m := n + 1) (n := n + 2)
      (by omega) (by omega)
  -- (b) three distinct fixed points and the two realizing swaps
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :
      ∃ a ∈ (g.supportᶜ : Finset α), ∃ b ∈ (g.supportᶜ : Finset α),
        ∃ c ∈ (g.supportᶜ : Finset α), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    have h3 : 2 < (g.supportᶜ : Finset α).card := by
      rw [Finset.card_compl, hgp, ← Nat.card_eq_fintype_card]
      omega
    obtain ⟨a, b, c, ha, hb, hc, h₁, h₂, h₃⟩ := Finset.two_lt_card_iff.mp h3
    exact ⟨a, ha, b, hb, c, hc, h₁, h₂, h₃⟩
  -- membership bookkeeping for the pointwise stabilizer `F`
  set F : Subgroup (Perm α) :=
    G ⊓ fixingSubgroup (Perm α) ((↑g.supportᶜ : Set α)) with hFdef
  have hgF : g ∈ F := by
    rw [hFdef, Subgroup.mem_inf]
    refine ⟨hg, ?_⟩
    rw [mem_fixingSubgroup_iff]
    intro y hy
    exact notMem_support.mp (by simpa using hy)
  have hordg : orderOf g = p := hgc.orderOf.trans hgp
  have hcardF : Nat.card F ∣ Nat.factorial p := by
    have := card_inf_fixing_dvd_factorial G g
    rwa [hgp] at this
  have hFle : F ≤ G := inf_le_left
  have hFfix : ∀ σ ∈ F, ∀ b' ∈ (g.supportᶜ : Finset α), (σ : Perm α) b' = b' := by
    intro σ hσ b' hb'
    exact fixes_compl_of_mem_inf_fixing hσ b' (Finset.mem_compl.mp hb')
  -- invariance of `supportᶜ` under a permutation mapping it into itself
  have hkinv : ∀ k : Perm α,
      (∀ b' ∈ (g.supportᶜ : Finset α), k b' ∈ (g.supportᶜ : Finset α)) →
      ∀ b' : α, b' ∈ (g.supportᶜ : Finset α) ↔ k b' ∈ (g.supportᶜ : Finset α) := by
    intro k hk b'
    have himg : (g.supportᶜ : Finset α).image k = (g.supportᶜ : Finset α) := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact hk z hz
      · rw [Finset.card_image_of_injective _ k.injective]
    refine ⟨hk b', fun hkb => ?_⟩
    rw [← himg] at hkb
    obtain ⟨z, hz, hzb⟩ := Finset.mem_image.mp hkb
    rwa [← k.injective hzb]
  -- a permutation mapping `supportᶜ` into itself conjugates `F` into `F`
  have hconjF : ∀ k : Perm α, k ∈ G →
      (∀ b' ∈ (g.supportᶜ : Finset α), k b' ∈ (g.supportᶜ : Finset α)) →
      ∀ q ∈ F, k * q * k⁻¹ ∈ F := by
    intro k hkG hk q hq
    rw [hFdef, Subgroup.mem_inf]
    refine ⟨G.mul_mem (G.mul_mem hkG (hFle hq)) (G.inv_mem hkG), ?_⟩
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hy' : y ∈ (g.supportᶜ : Finset α) := by simpa using hy
    have h1 : k⁻¹ y ∈ (g.supportᶜ : Finset α) :=
      (hkinv k hk (k⁻¹ y)).mpr (by simpa using hy')
    have h2 : q (k⁻¹ y) = k⁻¹ y := hFfix q hq _ h1
    change k (q (k⁻¹ y)) = y
    rw [h2]
    simp
  -- support inclusion for permutations supported in `supportᶜ`
  have hτmaps : ∀ τ : Perm α, τ.support ⊆ (g.supportᶜ : Finset α) →
      ∀ b' ∈ (g.supportᶜ : Finset α), τ b' ∈ (g.supportᶜ : Finset α) := by
    intro τ hτ b' hb'
    by_cases hbs : b' ∈ τ.support
    · exact hτ (apply_mem_support.mpr hbs)
    · rw [notMem_support.mp hbs]
      exact hb'
  -- realize a permutation supported in `supportᶜ` by an element of `G`
  -- normalizing `⟨g⟩` and agreeing with it there
  have hrealize : ∀ τ : Perm α, τ.support ⊆ (g.supportᶜ : Finset α) →
      ∃ x : Perm α, x ∈ G ∧
        x ∈ Subgroup.normalizer (Subgroup.zpowers g) ∧
        ∀ b' ∈ (g.supportᶜ : Finset α), x b' = τ b' := by
    intro τ hτ
    obtain ⟨k, hkG, hkagree⟩ := exists_agree_of_isMultiplyPretransitive hMT τ
    have hkmaps : ∀ b' ∈ (g.supportᶜ : Finset α),
        k b' ∈ (g.supportᶜ : Finset α) := by
      intro b' hb'
      rw [hkagree b' hb']
      exact hτmaps τ hτ b' hb'
    obtain ⟨h, hhF, hnorm⟩ := exists_mul_mem_normalizer_zpowers hp hgF hordg
      hcardF (hconjF k hkG hkmaps)
    refine ⟨h * k, G.mul_mem (hFle hhF) hkG, hnorm, fun b' hb' => ?_⟩
    have h1 : k b' = τ b' := hkagree b' hb'
    have h2 : τ b' ∈ (g.supportᶜ : Finset α) := hτmaps τ hτ b' hb'
    change h (k b') = τ b'
    rw [h1]
    exact hFfix h hhF _ h2
  -- the two swaps and their realizations
  have hτ₁supp : (Equiv.swap a b).support ⊆ (g.supportᶜ : Finset α) := by
    rw [support_swap hab]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ha
    · rwa [Finset.mem_singleton.mp hy]
  have hτ₂supp : (Equiv.swap a c).support ⊆ (g.supportᶜ : Finset α) := by
    rw [support_swap hac]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ha
    · rwa [Finset.mem_singleton.mp hy]
  obtain ⟨x₁, hx₁G, hx₁n, hx₁a⟩ := hrealize (Equiv.swap a b) hτ₁supp
  obtain ⟨x₂, hx₂G, hx₂n, hx₂a⟩ := hrealize (Equiv.swap a c) hτ₂supp
  -- (c) the commutator and its `p`-th power
  set t : Perm α := ⁅Equiv.swap a b, Equiv.swap a c⁆ with htdef
  have htsupp : t.support ⊆ (g.supportᶜ : Finset α) := by
    rw [htdef, commutatorElement_def]
    refine le_trans (support_mul_le _ _) (sup_le (le_trans (support_mul_le _ _)
      (sup_le (le_trans (support_mul_le _ _) (sup_le hτ₁supp hτ₂supp)) ?_)) ?_)
    · rw [support_inv]
      exact hτ₁supp
    · rw [support_inv]
      exact hτ₂supp
  have hthree : t.IsThreeCycle := by
    apply isThreeCycle_commutator_of_unique_common_moved
      (a := a) (x := Equiv.swap a b) (y := Equiv.swap a c)
    · rw [Equiv.swap_apply_left]
      exact Ne.symm hab
    · rw [Equiv.swap_apply_left]
      exact Ne.symm hac
    · intro b' hb'
      by_cases hbb : b' = b
      · right
        subst hbb
        exact Equiv.swap_apply_of_ne_of_ne hb' hbc
      · left
        exact Equiv.swap_apply_of_ne_of_ne hb' hbb
  set x : Perm α := ⁅x₁, x₂⁆ with hxdef
  have hxG : x ∈ G := by
    rw [hxdef, commutatorElement_def]
    exact G.mul_mem (G.mul_mem (G.mul_mem hx₁G hx₂G) (G.inv_mem hx₁G))
      (G.inv_mem hx₂G)
  have hxg : Commute x g := commute_commutator_of_mem_normalizer hx₁n hx₂n
  -- `x` agrees with `t` on `supportᶜ`
  have hΛ₁ : ∀ b', b' ∈ ((g.supportᶜ : Finset α) : Set α) ↔
      Equiv.swap a b b' ∈ ((g.supportᶜ : Finset α) : Set α) := by
    intro b'
    simpa using hkinv (Equiv.swap a b) (hτmaps _ hτ₁supp) b'
  have hΛ₂ : ∀ b', b' ∈ ((g.supportᶜ : Finset α) : Set α) ↔
      Equiv.swap a c b' ∈ ((g.supportᶜ : Finset α) : Set α) := by
    intro b'
    simpa using hkinv (Equiv.swap a c) (hτmaps _ hτ₂supp) b'
  have hxt : ∀ b' ∈ ((g.supportᶜ : Finset α) : Set α), x b' = t b' := by
    rw [hxdef, htdef]
    exact commutator_apply_eq_of_agree hΛ₁ hΛ₂
      (fun b' hb' => hx₁a b' (by simpa using hb'))
      (fun b' hb' => hx₂a b' (by simpa using hb'))
  -- `x ^ p` is trivial on the support …
  obtain ⟨hxsupp, hmem⟩ := hgc.commute_iff.mp hxg
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hxgj : ∀ b' ∈ ((g.support : Finset α) : Set α), x b' = (g ^ j) b' := by
    intro b' hb'
    have hb'' : b' ∈ g.support := by simpa using hb'
    rw [hj]
    rw [ofSubtype_apply_of_mem (x.subtypePerm hxsupp) hb'']
    rfl
  have hgjinv : ∀ b', b' ∈ ((g.support : Finset α) : Set α) ↔
      (g ^ j) b' ∈ ((g.support : Finset α) : Set α) := by
    intro b'
    simp
  have hxp_supp : ∀ b' ∈ g.support, (x ^ p) b' = b' := by
    intro b' hb'
    have := pow_apply_eq_of_agree hgjinv hxgj p b' (by simpa using hb')
    rw [this]
    have hgp1 : (g ^ j) ^ p = 1 := by
      have hg1 : g ^ p = 1 := by
        rw [← hordg]
        exact pow_orderOf_eq_one g
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg1,
        one_zpow]
    rw [hgp1]
    rfl
  -- … and agrees with `t ^ p` on the complement
  have htinv : ∀ y, y ∈ ((g.supportᶜ : Finset α) : Set α) ↔
      t y ∈ ((g.supportᶜ : Finset α) : Set α) := by
    intro y
    simpa using hkinv t (hτmaps t htsupp) y
  have hxp_compl : ∀ b' ∈ (g.supportᶜ : Finset α), (x ^ p) b' = (t ^ p) b' :=
    fun b' hb' => pow_apply_eq_of_agree htinv hxt p b' (by simpa using hb')
  -- hence `x ^ p = t ^ p`, a three-cycle
  have hxp : x ^ p = t ^ p := by
    ext b'
    by_cases hb' : b' ∈ g.support
    · rw [hxp_supp b' hb']
      have : b' ∉ (t ^ p).support := fun hc =>
        Finset.mem_compl.mp (htsupp (support_pow_le t p hc)) hb'
      exact (notMem_support.mp this).symm
    · exact hxp_compl b' (Finset.mem_compl.mpr hb')
  have hp3' : ¬ 3 ∣ p := by
    intro hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd) with h | h
    · omega
    · exact hp3 h.symm
  have htp : (t ^ p).IsThreeCycle := by
    have horder : orderOf t = 3 := hthree.orderOf
    have hmod : t ^ p = t ^ (p % 3) := by
      rw [← horder]
      exact (pow_mod_orderOf t p).symm
    have hmod3 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hmod3 with h | h
    · rw [hmod, h, pow_one]
      exact hthree
    · rw [hmod, h]
      have ht2 : t ^ 2 = t⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have h31 : t ^ 3 = 1 := by
          rw [← horder]
          exact pow_orderOf_eq_one t
        have h32 : t ^ 2 * t = t ^ 3 := by
          rw [← pow_succ]
        rw [h32, h31]
      rw [ht2]
      exact hthree.inv
  rw [← hxp] at htp
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG
    htp (G.pow_mem hxG p)

end Main

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
