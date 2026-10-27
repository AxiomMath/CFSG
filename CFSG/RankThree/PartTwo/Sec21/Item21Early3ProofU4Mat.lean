module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item21Early3Proof

open Matrix

variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem sq_add_add_one_eq_zero {β : K} (h3 : β ^ 3 = 1) (h1 : β ≠ 1) : β ^ 2 + β + 1 = 0 := by
  have h : (β - 1) * (β ^ 2 + β + 1) = 0 := by
    have : (β - 1) * (β ^ 2 + β + 1) = β ^ 3 - 1 := by ring
    rw [this, h3, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact h

omit [CharP K 2] in
theorem ne_zero_of_pow_three {β : K} (h3 : β ^ 3 = 1) : β ≠ 0 := by
  rintro rfl
  norm_num at h3

theorem add_self_eq_zero' (x : K) : x + x = 0 := by
  rw [← two_mul, CharTwo.two_eq_zero, zero_mul]

theorem eq_of_add_eq_zero {x y : K} (h : x + y = 0) : x = y := by
  have : x = -y := eq_neg_of_add_eq_zero_left h
  rw [this, CharTwo.neg_eq]

theorem add_inv_eq_one {β : K} (h3 : β ^ 3 = 1) (h1 : β ≠ 1) : β + β⁻¹ = 1 := by
  have h0 := ne_zero_of_pow_three h3
  have hq := sq_add_add_one_eq_zero h3 h1
  have hinv : β⁻¹ = β ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)).symm
  rw [hinv]
  have : β + β ^ 2 = β ^ 2 + β + 1 + 1 := by
    rw [add_assoc (β ^ 2 + β), add_self_eq_zero', add_zero, add_comm]
  rw [this, hq, zero_add]

theorem ratio_add_ratio_of_eq (x : K) : x * x⁻¹ + x * x⁻¹ = 0 :=
  add_self_eq_zero' _

theorem ratio_add_ratio_of_ne {x y : K} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (h : x ≠ y) :
    y * x⁻¹ + x * y⁻¹ = 1 := by
  have hx0 := ne_zero_of_pow_three hx
  have hy0 := ne_zero_of_pow_three hy
  have hβ3 : (y * x⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have hβ1 : y * x⁻¹ ≠ 1 := fun h1 => h ((mul_inv_eq_one₀ hx0).mp h1).symm
  have := add_inv_eq_one hβ3 hβ1
  rwa [mul_inv_rev, inv_inv] at this

theorem sq_eq_mul_of_distinct {x y z : K} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : z ^ 2 = x * y := by
  have hx0 := ne_zero_of_pow_three hx
  set β := y * x⁻¹ with hβ
  set γ := z * x⁻¹ with hγ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have hγ3 : γ ^ 3 = 1 := by rw [hγ, mul_pow, inv_pow, hx, hz, inv_one, mul_one]
  have hβ1 : β ≠ 1 := fun h1 => hxy ((mul_inv_eq_one₀ hx0).mp h1).symm
  have hγ1 : γ ≠ 1 := fun h1 => hxz ((mul_inv_eq_one₀ hx0).mp h1).symm
  have hβγ : β ≠ γ := fun h1 => hyz (by
    have := congrArg (· * x) h1
    simpa [hβ, hγ, mul_assoc, inv_mul_cancel₀ hx0] using this)
  have hqβ := sq_add_add_one_eq_zero hβ3 hβ1
  have hqγ := sq_add_add_one_eq_zero hγ3 hγ1
  have hsum : (β - γ) * (β + γ + 1) = 0 := by
    have : (β - γ) * (β + γ + 1) = (β ^ 2 + β + 1) - (γ ^ 2 + γ + 1) := by ring
    rw [this, hqβ, hqγ, sub_self]
  have hγβ : γ = β + 1 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd (sub_eq_zero.mp h) hβγ
    · have h' : γ + (β + 1) = 0 := by rw [← h]; ring
      exact eq_of_add_eq_zero h'
  have hγ2 : γ ^ 2 = β := by
    have h1 : γ ^ 2 = β ^ 2 + 1 := by
      rw [hγβ, add_sq, mul_one, one_pow, two_mul, add_self_eq_zero' β, add_zero]
    have h2 : β ^ 2 = β + 1 := by
      have := hqβ
      have h3 : β ^ 2 + (β + 1) = 0 := by rw [← this]; ring
      exact eq_of_add_eq_zero h3
    rw [h1, h2, add_assoc, add_self_eq_zero', add_zero]
  have : z = γ * x := by rw [hγ, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  have hy' : y = β * x := by rw [hβ, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  rw [this, hy', mul_pow, hγ2]
  have : x ^ 2 = x * x := sq x
  rw [this]
  ring

structure MatHyp (bar : K →+* K) (X : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4 → K) : Prop where
  cube : ∀ i, b i ^ 3 = 1
  herm : ∀ i j, bar (X j i) = X i j
  sq : ∀ i j, ∑ k, X i k * X k j = 0
  blk : ∀ i j, a i ≠ a j → X i j = 0
  comm : ∀ i j, ∑ k, X i k * (b k * X k j * (b j)⁻¹) = ∑ k, b i * X i k * (b k)⁻¹ * X k j

namespace MatHyp

variable {bar : K →+* K} {X : Matrix (Fin 4) (Fin 4) K} {a b : Fin 4 → K}

omit [CharP K 2] in
theorem perm (h : MatHyp bar X a b) (σ : Equiv.Perm (Fin 4)) :
    MatHyp bar (fun i j => X (σ i) (σ j)) (a ∘ σ) (b ∘ σ) where
  cube i := h.cube (σ i)
  herm i j := h.herm (σ i) (σ j)
  sq i j := (Equiv.sum_comp σ (fun k => X (σ i) k * X k (σ j))).trans (h.sq (σ i) (σ j))
  blk i j hij := h.blk (σ i) (σ j) hij
  comm i j := by
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp σ (fun k => X (σ i) k * (b k * X k (σ j) * (b (σ j))⁻¹)),
      Equiv.sum_comp σ (fun k => b (σ i) * X (σ i) k * (b k)⁻¹ * X k (σ j))]
    exact h.comm (σ i) (σ j)

omit [CharP K 2] in
theorem norm_ne_zero {x : K} (hx : x ≠ 0) : x * bar x ≠ 0 :=
  mul_ne_zero hx ((map_ne_zero bar).mpr hx)

omit [CharP K 2] in
theorem norm_symm (h : MatHyp bar X a b) (i j : Fin 4) :
    X j i * bar (X j i) = X i j * bar (X i j) := by
  rw [h.herm i j, ← h.herm j i, mul_comm]

theorem rowSum (h : MatHyp bar X a b) (i : Fin 4) :
    ∑ k, (b k * (b i)⁻¹ + b i * (b k)⁻¹) * (X i k * bar (X i k)) = 0 := by
  have hc := h.comm i i
  have hb0 : ∀ k, b k ≠ 0 := fun k => ne_zero_of_pow_three (h.cube k)
  have e1 : ∀ k, X i k * (b k * X k i * (b i)⁻¹) =
      b k * (b i)⁻¹ * (X i k * bar (X i k)) := by
    intro k
    rw [← h.herm k i]
    ring
  have e2 : ∀ k, b i * X i k * (b k)⁻¹ * X k i = b i * (b k)⁻¹ * (X i k * bar (X i k)) := by
    intro k
    rw [← h.herm k i]
    ring
  simp only [e1, e2] at hc
  have : ∑ k, (b k * (b i)⁻¹ + b i * (b k)⁻¹) * (X i k * bar (X i k)) =
      ∑ k, b k * (b i)⁻¹ * (X i k * bar (X i k)) +
        ∑ k, b i * (b k)⁻¹ * (X i k * bar (X i k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, hc, add_self_eq_zero']

theorem weight_eq (_h : MatHyp bar X a b) {i k : Fin 4} (hik : b i = b k) :
    b k * (b i)⁻¹ + b i * (b k)⁻¹ = 0 := by
  rw [hik]
  exact ratio_add_ratio_of_eq (b k)

theorem weight_ne (h : MatHyp bar X a b) {i k : Fin 4} (hik : b i ≠ b k) :
    b k * (b i)⁻¹ + b i * (b k)⁻¹ = 1 :=
  ratio_add_ratio_of_ne (h.cube i) (h.cube k) hik

end MatHyp

variable {bar : K →+* K} {X : Matrix (Fin 4) (Fin 4) K} {a b : Fin 4 → K}

theorem eq_zero_of_block_two (h : MatHyp bar X a b) (h01 : b 0 ≠ b 1) (h2 : a 0 ≠ a 2)
    (h3 : a 0 ≠ a 3) : X 0 1 = 0 := by
  have hr := h.rowSum 0
  rw [Fin.sum_univ_four, h.weight_eq rfl, h.weight_ne h01, h.blk 0 2 h2, h.blk 0 3 h3] at hr
  simp only [zero_mul, one_mul, map_zero, mul_zero, add_zero, zero_add] at hr
  by_contra hne
  exact MatHyp.norm_ne_zero hne hr

theorem eq_zero_of_block_three (h : MatHyp bar X a b) (h01 : b 0 ≠ b 1) (ha01 : a 0 = a 1)
    (ha02 : a 0 = a 2) (h3 : a 0 ≠ a 3) : X 0 1 = 0 := by
  have h13 : a 1 ≠ a 3 := ha01 ▸ h3
  have h23 : a 2 ≠ a 3 := ha02 ▸ h3
  have hX03 := h.blk 0 3 h3
  have hX13 := h.blk 1 3 h13
  have hX23 := h.blk 2 3 h23
  have hX31 := h.blk 3 1 (Ne.symm h13)
  by_contra hne
  have hN01 := MatHyp.norm_ne_zero (bar := bar) hne
  by_cases hb20 : b 0 = b 2
  ·
    have hr := h.rowSum 0
    rw [Fin.sum_univ_four, h.weight_eq rfl, h.weight_ne h01, h.weight_eq hb20, hX03] at hr
    simp only [zero_mul, one_mul, map_zero, mul_zero, add_zero, zero_add] at hr
    exact hN01 hr
  by_cases hb21 : b 1 = b 2
  ·
    have hr := h.rowSum 1
    rw [Fin.sum_univ_four, h.weight_ne (Ne.symm h01), h.weight_eq rfl, h.weight_eq hb21,
      hX13] at hr
    simp only [zero_mul, one_mul, map_zero, mul_zero, add_zero] at hr
    rw [h.norm_symm 0 1] at hr
    exact hN01 hr
  have hr0 := h.rowSum 0
  rw [Fin.sum_univ_four, h.weight_eq rfl, h.weight_ne h01, h.weight_ne hb20, hX03] at hr0
  simp only [zero_mul, one_mul, map_zero, mul_zero, add_zero, zero_add] at hr0
  have hr1 := h.rowSum 1
  rw [Fin.sum_univ_four, h.weight_ne (Ne.symm h01), h.weight_eq rfl, h.weight_ne hb21,
    hX13] at hr1
  simp only [zero_mul, one_mul, map_zero, mul_zero, add_zero] at hr1
  have hN02 : X 0 2 * bar (X 0 2) ≠ 0 := by
    rw [← eq_of_add_eq_zero hr0]
    exact hN01
  have hN12 : X 1 2 * bar (X 1 2) ≠ 0 := by
    rw [h.norm_symm 0 1] at hr1
    rw [← eq_of_add_eq_zero hr1]
    exact hN01
  have hX02 : X 0 2 ≠ 0 := fun h0 => hN02 (by rw [h0, zero_mul])
  have hX21 : X 2 1 ≠ 0 := by
    rw [← h.herm 2 1]
    exact (map_ne_zero bar).mpr (fun h0 => hN12 (by rw [h0, zero_mul]))
  have hb0 : ∀ k, b k ≠ 0 := fun k => ne_zero_of_pow_three (h.cube k)
  have hsq2 : b 2 ^ 2 = b 0 * b 1 :=
    sq_eq_mul_of_distinct (h.cube 0) (h.cube 1) (h.cube 2) h01 hb20 hb21
  have hc := h.comm 0 1
  rw [Fin.sum_univ_four, Fin.sum_univ_four, hX03, hX31] at hc
  have hX0011 : X 0 0 = X 1 1 := by
    have e2 : X 0 2 * (b 2 * X 2 1 * (b 1)⁻¹) = b 0 * X 0 2 * (b 2)⁻¹ * X 2 1 := by
      have : b 2 * (b 1)⁻¹ = b 0 * (b 2)⁻¹ := by
        have hb1 := hb0 1
        have hb2 := hb0 2
        calc b 2 * (b 1)⁻¹ = b 2 * (b 1)⁻¹ * (b 2 * (b 2)⁻¹) := by
              rw [mul_inv_cancel₀ hb2, mul_one]
          _ = b 2 ^ 2 * (b 1)⁻¹ * (b 2)⁻¹ := by ring
          _ = b 0 * b 1 * (b 1)⁻¹ * (b 2)⁻¹ := by rw [hsq2]
          _ = b 0 * (b 2)⁻¹ := by rw [mul_assoc (b 0), mul_inv_cancel₀ hb1, mul_one]
      calc X 0 2 * (b 2 * X 2 1 * (b 1)⁻¹) = X 0 2 * X 2 1 * (b 2 * (b 1)⁻¹) := by ring
        _ = X 0 2 * X 2 1 * (b 0 * (b 2)⁻¹) := by rw [this]
        _ = b 0 * X 0 2 * (b 2)⁻¹ * X 2 1 := by ring
    have hc' : X 0 0 * (b 0 * X 0 1 * (b 1)⁻¹) + X 0 1 * (b 1 * X 1 1 * (b 1)⁻¹) =
        b 0 * X 0 0 * (b 0)⁻¹ * X 0 1 + b 0 * X 0 1 * (b 1)⁻¹ * X 1 1 := by
      have := hc
      rw [e2] at this
      simp only [zero_mul, mul_zero, add_zero] at this
      linear_combination this
    have e3 : (X 0 0 - X 1 1) * X 0 1 * (b 0 * (b 1)⁻¹ - 1) = 0 := by
      have hb00 : b 0 * (b 0)⁻¹ = 1 := mul_inv_cancel₀ (hb0 0)
      have hb11 : b 1 * (b 1)⁻¹ = 1 := mul_inv_cancel₀ (hb0 1)
      linear_combination (X 0 0 * X 0 1 * hb00 - X 0 1 * X 1 1 * hb11) + hc'
    have hβ : b 0 * (b 1)⁻¹ - 1 ≠ 0 := by
      intro h0
      apply h01
      have := sub_eq_zero.mp h0
      exact (mul_inv_eq_one₀ (hb0 1)).mp this
    rcases mul_eq_zero.mp e3 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact sub_eq_zero.mp h2
      · exact absurd h2 hne
    · exact absurd h1 hβ
  have hs := h.sq 0 1
  rw [Fin.sum_univ_four, hX03, ← hX0011] at hs
  have : X 0 2 * X 2 1 = 0 := by
    have e : X 0 0 * X 0 1 + X 0 1 * X 0 0 = 0 := by
      rw [mul_comm (X 0 1), add_self_eq_zero']
    linear_combination hs - e
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hX02 h1
  · exact hX21 h1

theorem eq_zero_of_ne (h : MatHyp bar X a b) (hnc : ∃ i j, a i ≠ a j) {i j : Fin 4}
    (hb : b i ≠ b j) : X i j = 0 := by
  have hij : i ≠ j := fun e => hb (e ▸ rfl)
  by_cases ha : a i = a j
  swap
  · exact h.blk i j ha
  set τ₁ := Equiv.swap (0 : Fin 4) i with hτ₁
  set j' := τ₁ j with hj'
  have hj'0 : j' ≠ 0 := by
    intro h0
    apply hij
    have : τ₁ j' = τ₁ 0 := by rw [h0]
    rw [hj', Equiv.swap_apply_self, hτ₁, Equiv.swap_apply_left] at this
    exact this.symm
  set τ₂ := Equiv.swap (1 : Fin 4) j' with hτ₂
  set σ := τ₁ * τ₂ with hσ
  have hσ0 : σ 0 = i := by
    rw [hσ, Equiv.Perm.mul_apply, hτ₂, Equiv.swap_apply_of_ne_of_ne (by decide) hj'0.symm,
      hτ₁, Equiv.swap_apply_left]
  have hσ1 : σ 1 = j := by
    rw [hσ, Equiv.Perm.mul_apply, hτ₂, Equiv.swap_apply_left, hj', hτ₁,
      Equiv.swap_apply_self]
  have h' := h.perm σ
  have hb' : (b ∘ σ) 0 ≠ (b ∘ σ) 1 := by simpa [hσ0, hσ1] using hb
  have ha' : (a ∘ σ) 0 = (a ∘ σ) 1 := by simpa [hσ0, hσ1] using ha
  have hout : ∃ m : Fin 4, (a ∘ σ) 0 ≠ (a ∘ σ) m := by
    obtain ⟨p, q, hpq⟩ := hnc
    by_cases hp : a i = a p
    · refine ⟨σ.symm q, ?_⟩
      simp only [Function.comp_apply, Equiv.apply_symm_apply, hσ0]
      rw [hp]
      exact hpq
    · refine ⟨σ.symm p, ?_⟩
      simp only [Function.comp_apply, Equiv.apply_symm_apply, hσ0]
      exact hp
  obtain ⟨m, hm⟩ := hout
  have hm01 : m ≠ 0 ∧ m ≠ 1 := ⟨fun e => hm (e ▸ rfl), fun e => hm (e ▸ ha')⟩
  have hres : (fun i j => X (σ i) (σ j)) 0 1 = 0 := by
    by_cases h2 : (a ∘ σ) 0 = (a ∘ σ) 2
    ·
      have h3 : (a ∘ σ) 0 ≠ (a ∘ σ) 3 := by
        intro h3
        fin_cases m
        · exact hm01.1 rfl
        · exact hm01.2 rfl
        · exact hm h2
        · exact hm h3
      exact eq_zero_of_block_three h' hb' ha' h2 h3
    · by_cases h3 : (a ∘ σ) 0 = (a ∘ σ) 3
      ·
        have h'' := h'.perm (Equiv.swap 2 3)
        have hsw0 : (Equiv.swap (2 : Fin 4) 3) 0 = 0 := by decide
        have hsw1 : (Equiv.swap (2 : Fin 4) 3) 1 = 1 := by decide
        have hsw2 : (Equiv.swap (2 : Fin 4) 3) 2 = 3 := by decide
        have hsw3 : (Equiv.swap (2 : Fin 4) 3) 3 = 2 := by decide
        have := eq_zero_of_block_three h''
          (by simpa only [Function.comp_apply, hsw0, hsw1] using hb')
          (by simpa only [Function.comp_apply, hsw0, hsw1] using ha')
          (by simpa only [Function.comp_apply, hsw0, hsw2] using h3)
          (by simpa only [Function.comp_apply, hsw0, hsw3] using h2)
        simpa only [hsw0, hsw1] using this
      · exact eq_zero_of_block_two h' hb' h2 h3
  simpa [hσ0, hσ1] using hres

end Item21Early3Proof

end CFSG.RankThree.PartTwo.Sec21
