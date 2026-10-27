module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open Equiv Equiv.Perm

variable {Ω : Type*} [DecidableEq Ω]

@[expose] def IsSwapGroup (H : Subgroup (Perm Ω)) : Prop :=
  ∀ d ∈ H, ∀ x, d x = x ∨ swap x (d x) ∈ H

section Young

variable [Fintype Ω] {H : Subgroup (Perm Ω)}

private theorem mem_of_orbit (hH : IsSwapGroup H) :
    ∀ (n : ℕ) (σ : Perm Ω), (Finset.univ.filter fun x => σ x ≠ x).card = n →
      (∀ z, ∃ d ∈ H, d z = σ z) → σ ∈ H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hn hσ
    by_cases h0 : ∀ x, σ x = x
    · have : σ = 1 := Equiv.ext h0
      rw [this]
      exact H.one_mem
    · push Not at h0
      obtain ⟨x, hx⟩ := h0
      obtain ⟨d, hd, hdx⟩ := hσ x
      have hτ : swap x (σ x) ∈ H := by
        have := hH d hd x
        rw [hdx] at this
        exact this.resolve_left hx
      set τ : Perm Ω := swap x (σ x) with hτdef
      have hσ' : ∀ z, ∃ d' ∈ H, d' z = (τ * σ) z := by
        intro z
        obtain ⟨d, hd, hdz⟩ := hσ z
        exact ⟨τ * d, H.mul_mem hτ hd, by simp [hdz]⟩
      have hfix : ∀ z, σ z = z → (τ * σ) z = z := by
        intro z hσz
        rw [Perm.mul_apply, hσz, hτdef]
        apply swap_apply_of_ne_of_ne
        · rintro rfl
          exact hx hσz
        · intro h
          apply hx
          apply σ.injective
          rw [h] at hσz
          exact hσz
      have hsub : (Finset.univ.filter fun z => (τ * σ) z ≠ z) ⊂
          (Finset.univ.filter fun z => σ z ≠ z) := by
        have hle : (Finset.univ.filter fun z => (τ * σ) z ≠ z) ⊆
            (Finset.univ.filter fun z => σ z ≠ z) := by
          intro z hz
          rw [Finset.mem_filter] at hz ⊢
          exact ⟨Finset.mem_univ _, fun h => hz.2 (hfix z h)⟩
        refine (Finset.ssubset_iff_of_subset hle).2 ⟨x, ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hx⟩
        · rw [Finset.mem_filter]
          rintro ⟨-, h⟩
          apply h
          rw [Perm.mul_apply, hτdef]
          exact swap_apply_right _ _
      have := ih _ (hn ▸ Finset.card_lt_card hsub) (τ * σ) rfl hσ'
      have h2 : σ = τ * (τ * σ) := by
        rw [← mul_assoc, hτdef, swap_mul_self, one_mul]
      rw [h2]
      exact H.mul_mem hτ this

theorem IsSwapGroup.mem_of (hH : IsSwapGroup H) (σ : Perm Ω)
    (hσ : ∀ x, σ x = x ∨ swap x (σ x) ∈ H) : σ ∈ H := by
  refine mem_of_orbit hH _ σ rfl fun z => ?_
  rcases hσ z with h | h
  · exact ⟨1, H.one_mem, by simp [h]⟩
  · exact ⟨_, h, by simp⟩

end Young

section Matching

variable [Fintype Ω] {H : Subgroup (Perm Ω)}

theorem eq_of_swap_mem_swap_mem (hp : IsPGroup 2 H) {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z)
    (h1 : swap x y ∈ H) (h2 : swap x z ∈ H) : y = z := by
  by_contra hyz
  have hg : swap x y * swap x z ∈ H := H.mul_mem h1 h2
  obtain ⟨k, hk⟩ := hp ⟨_, hg⟩
  have h3 : orderOf (swap x y * swap x z) = 3 :=
    (isThreeCycle_swap_mul_swap_same hxy hxz hyz).orderOf
  have h4 : orderOf (swap x y * swap x z) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  rw [h3] at h4
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
  omega

theorem IsSwapGroup.apply_mem_pair (hH : IsSwapGroup H) (hp : IsPGroup 2 H) {a b : Ω}
    (hab : a ≠ b) (h : swap a b ∈ H) {d : Perm Ω} (hd : d ∈ H) : d a = a ∨ d a = b := by
  by_cases hda : d a = a
  · exact Or.inl hda
  · exact Or.inr (eq_of_swap_mem_swap_mem hp hab (fun e => hda e.symm) h
      ((hH d hd a).resolve_left hda)).symm

theorem isSwapGroup_iSup {ι : Sort*} (B : ι → Subgroup (Perm Ω)) (hB : ∀ i, IsSwapGroup (B i))
    (hp : IsPGroup 2 ↥(⨆ i, B i)) : IsSwapGroup (⨆ i, B i) := by
  intro d hd
  refine Subgroup.iSup_induction B
    (C := fun d => ∀ x, d x = x ∨ swap x (d x) ∈ ⨆ i, B i) hd ?_ (fun x => Or.inl rfl) ?_
  · intro i σ hσ x
    exact (hB i σ hσ x).imp_right fun h => Subgroup.mem_iSup_of_mem i h
  · intro σ τ hσ hτ x
    rw [Perm.mul_apply]
    by_cases hx : τ x = x
    · rw [hx]
      exact hσ x
    · have hτx := (hτ x).resolve_left hx
      by_cases hy : σ (τ x) = τ x
      · rw [hy]
        exact Or.inr hτx
      · have h := (hσ (τ x)).resolve_left hy
        by_cases hz : σ (τ x) = x
        · exact Or.inl hz
        · exfalso
          apply hz
          exact (eq_of_swap_mem_swap_mem hp hx (fun e => hy e.symm)
            (by rwa [swap_comm] at hτx) h).symm

open scoped Classical in
theorem odd_card_fixed (hp : IsPGroup 2 H) (hodd : Odd (Fintype.card Ω)) :
    Odd (Finset.univ.filter fun y : Ω => ∀ d ∈ H, d y = y).card := by
  classical
  have h := hp.card_modEq_card_fixedPoints Ω
  rw [Nat.card_eq_fintype_card] at h
  have h1 : Nat.card (MulAction.fixedPoints H Ω) =
      (Finset.univ.filter fun y : Ω => ∀ d ∈ H, d y = y).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [MulAction.mem_fixedPoints]
    exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d d.2⟩
  rw [← h1]
  have h' : Nat.card (MulAction.fixedPoints H Ω) % 2 = Fintype.card Ω % 2 := h.symm
  rw [Nat.odd_iff] at hodd ⊢
  exact h'.trans hodd

theorem exists_fixed_of_odd (hp : IsPGroup 2 H) (hodd : Odd (Fintype.card Ω)) :
    ∃ c : Ω, ∀ d ∈ H, d c = c := by
  classical
  have h2 := odd_card_fixed hp hodd
  obtain ⟨c, hc⟩ := Finset.card_pos.1 h2.pos
  exact ⟨c, (Finset.mem_filter.1 hc).2⟩

theorem fixed_trichotomy (hp : IsPGroup 2 H) (hodd : Odd (Fintype.card Ω)) {x : Ω}
    (hx : ∀ d ∈ H, d x = x) :
    (∃ f₁ f₂ : Ω, f₁ ≠ x ∧ f₂ ≠ x ∧ f₁ ≠ f₂ ∧ (∀ d ∈ H, d f₁ = f₁) ∧
      ∀ d ∈ H, d f₂ = f₂) ∨ ∀ y, (∀ d ∈ H, d y = y) → y = x := by
  classical
  by_cases hall : ∀ y, (∀ d ∈ H, d y = y) → y = x
  · exact Or.inr hall
  · left
    push Not at hall
    obtain ⟨y, hy, hyx⟩ := hall
    have hodd' := odd_card_fixed hp hodd
    set F := Finset.univ.filter fun y : Ω => ∀ d ∈ H, d y = y with hF
    have hxF : x ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
    have hyF : y ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
    have h2 : 2 ≤ F.card := by
      have : ({x, y} : Finset Ω) ⊆ F := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact hxF
        · rw [Finset.mem_singleton.1 hz]; exact hyF
      have h3 := Finset.card_le_card this
      rwa [Finset.card_pair (Ne.symm hyx)] at h3
    have h3 : 3 ≤ F.card := by
      rcases hodd' with ⟨k, hk⟩
      omega
    have h4 : 1 < (F.erase x).card := by
      rw [Finset.card_erase_of_mem hxF]
      omega
    obtain ⟨f₁, hf₁, f₂, hf₂, hne⟩ := Finset.one_lt_card.1 h4
    rw [Finset.mem_erase] at hf₁ hf₂
    exact ⟨f₁, f₂, hf₁.1, hf₂.1, hne, (Finset.mem_filter.1 hf₁.2).2,
      (Finset.mem_filter.1 hf₂.2).2⟩

end Matching

end CFSG.Quasithin.C124.YZ
