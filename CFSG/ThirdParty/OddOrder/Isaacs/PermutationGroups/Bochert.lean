/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.CycleCommutators

/-!
# Isaacs, Finite Group Theory — Ch. 8: Bochert's theorem (Thm 8.26)

Formalizes **Isaacs Thm 8.26** (Bochert, p. 238): a primitive subgroup
`G ≤ Sym(Ω)` with `|Ω| = n` that does not contain the alternating group has
index at least `⌊(n+1)/2⌋!` in the symmetric group
(`factorial_le_index_of_isPreprimitive`).

Proof: choose `Δ ⊆ Ω` of minimal size `m` with `S_Δ ∩ G = 1` (where `S_Δ` is
the pointwise stabilizer of `Δ` in `Sym(Ω)`, of order `(n-m)!`); distinct
elements of `S_Δ` represent distinct cosets of `G`, so `|S : G| ≥ (n-m)!`.
If `m > n/2` then minimality applied to `Ω - Δ` and to `Δ - {α}` produces
nonidentity `x, y ∈ G` moving exactly one common point, so `⁅x, y⁆ ∈ G` is a
`3`-cycle (Lem 8.25) and the `3`-cycle Jordan theorem forces
`Alt(Ω) ≤ G`, a contradiction; hence `m ≤ n/2` and `(n-m)! ≥ ⌊(n+1)/2⌋!`.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open Equiv Equiv.Perm MulAction

open scoped commutatorElement

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A permutation fixing `Δ` pointwise preserves `Δᶜ`. -/
private lemma mem_compl_iff_of_fixes {Δ : Finset α} {σ : Perm α}
    (hσ : ∀ b ∈ Δ, σ b = b) (b : α) : b ∈ Δᶜ ↔ σ b ∈ Δᶜ := by
  simp only [Finset.mem_compl]
  constructor
  · intro hb hc
    have h2 : σ b = b := σ.injective (hσ _ hc)
    rw [h2] at hc
    exact hb hc
  · intro hb hc
    exact hb ((hσ b hc).symm ▸ hc)

/-- The pointwise stabilizer of `Δ` in `Perm α` has order `|Δᶜ|!`. -/
private lemma card_fixingSubgroup_eq_factorial (Δ : Finset α) :
    Nat.card ↥(fixingSubgroup (Perm α) (↑Δ : Set α)) =
      Nat.factorial Δᶜ.card := by
  classical
  have hfix : ∀ σ : ↥(fixingSubgroup (Perm α) (↑Δ : Set α)), ∀ b ∈ Δ,
      (σ : Perm α) b = b := by
    intro σ b hb
    have h2 := σ.2
    rw [mem_fixingSubgroup_iff] at h2
    exact h2 b (by simpa using hb)
  set Φ : ↥(fixingSubgroup (Perm α) (↑Δ : Set α)) →* Perm {b // b ∈ Δᶜ} :=
    MonoidHom.mk'
      (fun σ => (σ : Perm α).subtypePerm fun b =>
        (mem_compl_iff_of_fixes (hfix σ) b).symm)
      (fun σ₁ σ₂ => by ext b; rfl) with hΦdef
  have hinj : Function.Injective Φ := by
    intro σ₁ σ₂ h
    ext b
    by_cases hb : b ∈ Δᶜ
    · exact congrArg (fun π : Perm {b // b ∈ Δᶜ} => (π ⟨b, hb⟩ : α)) h
    · rw [hfix σ₁ b (by simpa using hb), hfix σ₂ b (by simpa using hb)]
  have hsurj : Function.Surjective Φ := by
    intro π
    have hπ : ofSubtype π ∈ fixingSubgroup (Perm α) (↑Δ : Set α) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have hy' : ¬ y ∈ Δᶜ := by simpa using hy
      exact ofSubtype_apply_of_not_mem π hy'
    refine ⟨⟨ofSubtype π, hπ⟩, ?_⟩
    refine Equiv.ext fun b => Subtype.ext ?_
    change (ofSubtype π) ↑b = ↑(π b)
    rw [ofSubtype_apply_of_mem π b.2]
  rw [Nat.card_congr (MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toEquiv,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- **Isaacs Thm 8.26** (Bochert) — a primitive subgroup of `Perm α` on `n`
points that does not contain the alternating group has index at least
`⌊(n+1)/2⌋!` in the symmetric group. -/
theorem factorial_le_index_of_isPreprimitive {G : Subgroup (Perm α)}
    (hG : IsPreprimitive G α) (halt : ¬ alternatingGroup α ≤ G) :
    Nat.factorial ((Nat.card α + 1) / 2) ≤ G.index := by
  classical
  -- a minimal `Δ` whose pointwise stabilizer meets `G` trivially
  have hne : (Finset.univ.filter fun Δ : Finset α =>
      fixingSubgroup (Perm α) (↑Δ : Set α) ⊓ G = ⊥).Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [eq_bot_iff]
    intro σ hσ
    have h1 := (Subgroup.mem_inf.mp hσ).1
    rw [mem_fixingSubgroup_iff] at h1
    have : σ = 1 := by
      ext b
      exact h1 b (by simp)
    simp [this]
  obtain ⟨Δ, hΔmem, hΔmin⟩ := Finset.exists_min_image _ Finset.card hne
  have hΔ : fixingSubgroup (Perm α) (↑Δ : Set α) ⊓ G = ⊥ :=
    (Finset.mem_filter.mp hΔmem).2
  have hmin : ∀ Δ' : Finset α, Δ'.card < Δ.card →
      ∃ x : Perm α, x ∈ G ∧ x ≠ 1 ∧ ∀ b ∈ Δ', x b = b := by
    intro Δ' hlt
    by_contra hc
    have hbot : fixingSubgroup (Perm α) (↑Δ' : Set α) ⊓ G = ⊥ := by
      rw [eq_bot_iff]
      intro σ hσ
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hσ
      rw [mem_fixingSubgroup_iff] at h1
      rw [Subgroup.mem_bot]
      by_contra hσ1
      exact hc ⟨σ, h2, hσ1, fun b hb => h1 b (by simpa using hb)⟩
    have := hΔmin Δ' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbot⟩)
    omega
  -- the index bound `|Δᶜ|! ≤ |S : G|`
  have hindex : Nat.factorial Δᶜ.card ≤ G.index := by
    rw [← card_fixingSubgroup_eq_factorial Δ]
    have hinj : Function.Injective
        (fun σ : ↥(fixingSubgroup (Perm α) (↑Δ : Set α)) =>
          (QuotientGroup.mk (σ : Perm α) : Perm α ⧸ G)) := by
      intro σ₁ σ₂ h
      have h2 : (σ₁ : Perm α)⁻¹ * σ₂ ∈ G := (QuotientGroup.eq.mp h)
      have h3 : (σ₁ : Perm α)⁻¹ * σ₂ ∈
          fixingSubgroup (Perm α) (↑Δ : Set α) ⊓ G :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ σ₁.2) σ₂.2, h2⟩
      rw [hΔ, Subgroup.mem_bot, inv_mul_eq_one] at h3
      exact Subtype.ext h3
    exact Nat.card_le_card_of_injective _ hinj
  -- `|Δ| ≤ n / 2`: otherwise `G` contains a 3-cycle
  have hhalf : Δ.card ≤ Nat.card α / 2 := by
    by_contra hgt
    rw [not_le] at hgt
    -- `|Δᶜ| < |Δ|`, so some nonidentity `x ∈ G` fixes `Δᶜ` pointwise
    have hcompl : Δᶜ.card < Δ.card := by
      have := Finset.card_compl (α := α) Δ
      have hle := Finset.card_le_univ Δ
      rw [← Nat.card_eq_fintype_card] at *
      omega
    obtain ⟨x, hxG, hx1, hxfix⟩ := hmin Δᶜ hcompl
    -- a point moved by `x` lies in `Δ`
    obtain ⟨a, ha⟩ : ∃ a, x a ≠ a := by
      by_contra hc
      exact hx1 (Equiv.ext fun b => not_exists_not.mp hc b)
    have haΔ : a ∈ Δ := by
      by_contra hc
      exact ha (hxfix a (Finset.mem_compl.mpr hc))
    -- some nonidentity `y ∈ G` fixes `Δ - {a}` pointwise, and moves `a`
    obtain ⟨y, hyG, hy1, hyfix⟩ := hmin (Δ.erase a)
      (Finset.card_erase_lt_of_mem haΔ)
    have hya : y a ≠ a := by
      intro hya
      have hyΔ : y ∈ fixingSubgroup (Perm α) (↑Δ : Set α) ⊓ G := by
        rw [Subgroup.mem_inf]
        refine ⟨?_, hyG⟩
        rw [mem_fixingSubgroup_iff]
        intro b hb
        have hb' : b ∈ Δ := by simpa using hb
        rcases eq_or_ne b a with rfl | hba
        · exact hya
        · exact hyfix b (Finset.mem_erase.mpr ⟨hba, hb'⟩)
      rw [hΔ, Subgroup.mem_bot] at hyΔ
      exact hy1 hyΔ
    -- `x` and `y` move exactly one common point, so `⁅x,y⁆` is a 3-cycle
    have huniq : ∀ b : α, b ≠ a → x b = b ∨ y b = b := by
      intro b hba
      by_cases hb : b ∈ Δ
      · exact Or.inr (hyfix b (Finset.mem_erase.mpr ⟨hba, hb⟩))
      · exact Or.inl (hxfix b (Finset.mem_compl.mpr hb))
    have hthree : (⁅x, y⁆ : Perm α).IsThreeCycle :=
      isThreeCycle_commutator_of_unique_common_moved ha hya huniq
    have hcomm : ⁅x, y⁆ ∈ G := by
      rw [commutatorElement_def]
      exact G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG))
        (G.inv_mem hyG)
    exact halt
      (Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG
        hthree hcomm)
  -- conclude by monotonicity of the factorial
  refine le_trans (Nat.factorial_le ?_) hindex
  have h1 := Finset.card_compl (α := α) Δ
  rw [← Nat.card_eq_fintype_card] at h1
  omega

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
