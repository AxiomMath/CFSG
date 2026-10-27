module

public import CFSG.RankThree.PartOne.SEITZ5.UAlg
public import CFSG.RankThree.PartOne.SEITZ5.UCocycle
public import CFSG.RankThree.PartOne.SEITZ2.SUnPair

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem lam_eq_zero_of_basis [CharP K 2] (hσ : ∀ c, σ (σ c) = c) {ω ζ : K} (hζ : ζ ≠ 0)
    (hω : σ ω = ω ^ 2) (hω2 : ω ^ 2 + ω + 1 = 0) {lam : K →ₗ[fixSub σ] fixSub σ}
    (h1 : lam ζ = 0) (h2 : lam (ω * ζ) = 0) : lam = 0 := by
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω2
  refine LinearMap.ext fun c => ?_
  set b : K := c / ζ with hb
  have hbc : c = b * ζ := by rw [hb]; field_simp
  have hβ : σ (b + σ b) = b + σ b := by rw [map_add, hσ]; ring
  have hα : σ (ω ^ 2 * b + ω * σ b) = ω ^ 2 * b + ω * σ b := by
    have : σ (ω ^ 2) = ω := by
      rw [map_pow, hω, ← pow_mul, show 2 * 2 = 1 + 3 by norm_num, pow_add, hω3, pow_one, mul_one]
    rw [map_add, map_mul, map_mul, this, hω, hσ]
    ring
  let β : fixSub σ := ⟨b + σ b, hβ⟩
  let α : fixSub σ := ⟨ω ^ 2 * b + ω * σ b, hα⟩
  have hc : c = (α : K) * ζ + (β : K) * (ω * ζ) := by
    rw [hbc]
    show b * ζ = (ω ^ 2 * b + ω * σ b) * ζ + (b + σ b) * (ω * ζ)
    linear_combination (-(b * ζ)) * hω2 + (ζ * (b - ω * σ b)) * h2'
  rw [hc, map_add, lam_smul', lam_smul', h1, h2]
  simp

theorem sSub_eq_top [Finite K] [CharP K 2] {k : Subfield K} (hσ : ∀ c, σ (σ c) = c)
    (hk4 : Nat.card k = 4) {P : Frame σ n} {H : Subgroup (SUid σ n)} (hL : lSub P H = ⊤)
    (hF : ∃ s₀ : fixSub σ, s₀ ≠ 0 ∧ s₀ ≠ 1) {ω : K} (hω : σ ω = ω ^ 2)
    (hω2 : ω ^ 2 + ω + 1 = 0) {x y γ : fixSub σ} {ρ ζ : K} (hρ : ρ ∉ k) (hζ : ζ ≠ 0)
    (hρxy : ρ = x + ω ^ 2 * y) (hγ : (γ : K) = (x : K) ^ 2 + x * y + (y : K) ^ 2)
    (hE : ∃ t ∈ affGroup P H, Aff P t (u2 (1 : fixSub σ)) 0 0)
    (hW : ∃ t ∈ affGroup P H, Aff P t (u2 γ) 0 (ρ * ζ))
    (h1 : ∃ t ∈ affGroup P H, Aff P t (u2 y) 0 ζ)
    (hωg : ∃ t ∈ affGroup P H, Aff P t (u2 (x + y)) 0 (ω * ζ)) : sSub P H hL = ⊤ := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_contra hne
  have hlt : sSub P H hL < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨lam, hlam0, hS⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  obtain ⟨κ, hκ⟩ := lam_torus hS hF
  have : CharP (fixSub σ) 2 := inferInstance
  have : Finite (fixSub σ) := inferInstance
  obtain ⟨a, ha⟩ := isSquare_of_charTwo' x
  obtain ⟨sy, hsy⟩ := isSquare_of_charTwo' y
  obtain ⟨sxy, hsxy⟩ := isSquare_of_charTwo' (x + y)
  obtain ⟨sγ, hsγ⟩ := isSquare_of_charTwo' γ
  obtain ⟨tW, htW, hAW⟩ := hW
  obtain ⟨t1, ht1, hA1⟩ := h1
  obtain ⟨tω, htω, hAω⟩ := hωg
  have e1 := lam_generator hS hE hκ hsγ.symm htW hAW
  have e2 := lam_generator hS hE hκ hsy.symm ht1 hA1
  have e3 := lam_generator hS hE hκ hsxy.symm htω hAω
  have hρζ : ρ * ζ = (x : K) * ζ + (y : K) * (ω * ζ) + (y : K) * ζ := by
    rw [hρxy]
    linear_combination ((y : K) * ζ) * hω2 - ((y : K) * ζ * (ω + 1)) * h2
  have hlin : lam (ρ * ζ) = x * lam ζ + y * lam (ω * ζ) + y * lam ζ := by
    rw [hρζ, map_add, map_add, lam_smul', lam_smul', lam_smul']
  by_cases hκ0 : κ = 0
  · refine hlam0 (lam_eq_zero_of_basis hσ hζ hω hω2 ?_ ?_)
    · rw [e2, hκ0, zero_mul]
    · rw [e3, hκ0, zero_mul]
  · have key : sγ * sγ - sγ = x * (sy * sy - sy) + y * (sxy * sxy - sxy) + y * (sy * sy - sy) := by
      apply mul_left_cancel₀ hκ0
      have := hlin
      rw [e1, e2, e3] at this
      linear_combination this
    have hsγK : (sγ : K) * sγ = γ := by
      have := congrArg (fun z : fixSub σ => (z : K)) hsγ
      simp only [Subfield.coe_mul] at this
      exact this.symm
    have hsyK : (sy : K) * sy = y := by
      have := congrArg (fun z : fixSub σ => (z : K)) hsy
      simp only [Subfield.coe_mul] at this
      exact this.symm
    have hsxyK : (sxy : K) * sxy = (x : K) + y := by
      have := congrArg (fun z : fixSub σ => (z : K)) hsxy
      simp only [Subfield.coe_mul, Subfield.coe_add] at this
      exact this.symm
    have haxK : (a : K) * a = x := by
      have := congrArg (fun z : fixSub σ => (z : K)) ha
      simp only [Subfield.coe_mul] at this
      exact this.symm
    have keyK : (sγ : K) * sγ - sγ = (x : K) * ((sy : K) * sy - sy) +
        (y : K) * ((sxy : K) * sxy - sxy) + (y : K) * ((sy : K) * sy - sy) := by
      have := congrArg (fun z : fixSub σ => (z : K)) key
      simpa only [Subfield.coe_mul, Subfield.coe_add, Subfield.coe_sub] using this
    rw [hsγK, hsyK, hsxyK] at keyK
    have hK' : (γ : K) + sγ = (x : K) * (y + sy) + y * (x + y + sxy) + y * (y + sy) := by
      linear_combination keyK + ((sγ : K) - x * sy - y * sxy - y * sy) * h2
    have hf := eqn_of_relations (by rw [sq]; exact haxK) (by rw [sq]; exact hsyK)
      (by rw [sq]; exact hsxyK) (by rw [sq]; exact hsγK) hγ hK'
    have hξ := xi_pow_four hσ hω hω2 (mem_fixSub.1 a.2) (mem_fixSub.1 sy.2) hf
    have hξk : (a : K) + ω * sy ∈ k := mem_of_pow_card_eq_self (by norm_num) hk4 hξ
    have hρeq : ρ = ((a : K) + ω * sy) ^ 2 := by
      rw [hρxy, ← haxK, ← hsyK]
      linear_combination (-((a : K) * ω * sy)) * h2
    exact hρ (hρeq ▸ k.pow_mem hξk 2)

end CFSG.RankThree.PartOne.SEITZ5
