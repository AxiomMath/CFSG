module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Abel

public section

open scoped BigOperators

namespace CFSG.StandardType

theorem ggRC_fixed_vector_of_diag {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Finite W] (U : Submodule (ZMod p) W) (hU : U ≠ ⊤)
    (A Δ : Subgroup (W ≃ₗ[ZMod p] W)) (hΔA : Δ ≤ A)
    (hAU : ∀ a ∈ A, ∀ w, a w - w ∈ U)
    (hΔn : ∀ a ∈ A, ∀ d ∈ Δ, a * d * a⁻¹ ∈ Δ) (hΔp : ¬ p ∣ Nat.card Δ)
    (hUΔ : ∀ u ∈ U, (∀ d ∈ Δ, d u = u) → u = 0) :
    ∃ w : W, w ∉ U ∧ ∀ a ∈ A, a w = w := by
  obtain ⟨w₀, hw₀⟩ := SetLike.exists_not_mem_of_ne_top U hU
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype Δ := Fintype.ofInjective
    (fun d : Δ => ((d : W ≃ₗ[ZMod p] W) : W → W))
    (fun d₁ d₂ h => Subtype.ext (LinearEquiv.ext (fun x => congrFun h x)))
  have hΔp' : ¬ p ∣ Fintype.card Δ := by
    rw [← Nat.card_eq_fintype_card]
    exact hΔp
  let c : ZMod p := ((Fintype.card Δ : ZMod p))⁻¹
  have hc : (Fintype.card Δ : ZMod p) ≠ 0 := by
    intro hzero
    exact hΔp' ((ZMod.natCast_eq_zero_iff (Fintype.card Δ) p).mp hzero)
  have hc_mul : c * (Fintype.card Δ : ZMod p) = 1 := by
    dsimp only [c]
    exact inv_mul_cancel₀ hc
  let T : W := ∑ d : Δ, ((d : W ≃ₗ[ZMod p] W) w₀ - w₀)
  let S : W := ∑ d : Δ, (d : W ≃ₗ[ZMod p] W) w₀
  let u : W := c • T
  let w : W := c • S
  have hS : S = (Fintype.card Δ : ZMod p) • w₀ + T := by
    dsimp only [S, T]
    calc ∑ d : Δ, (d : W ≃ₗ[ZMod p] W) w₀
        = ∑ d : Δ, (w₀ + ((d : W ≃ₗ[ZMod p] W) w₀ - w₀)) := by
          apply Finset.sum_congr rfl
          intro d _
          abel
      _ = (∑ d : Δ, w₀) + ∑ d : Δ, ((d : W ≃ₗ[ZMod p] W) w₀ - w₀) :=
          Finset.sum_add_distrib
      _ = (Fintype.card Δ : ZMod p) • w₀ + ∑ d : Δ, ((d : W ≃ₗ[ZMod p] W) w₀ - w₀) := by
          rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hu_mem : u ∈ U := by
    dsimp only [u, T]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro d _
    exact hAU (d : W ≃ₗ[ZMod p] W) (hΔA d.2) w₀
  have hw_eq : w = w₀ + u := by
    dsimp only [w, u]
    rw [hS, smul_add, smul_smul, hc_mul, one_smul]
  have hw_ne : w ∉ U := by
    intro hwU
    have hw0U : w₀ ∈ U := by
      have hwu : w₀ = w - u := by rw [hw_eq]; abel
      rw [hwu]
      have : w + -u ∈ U := Submodule.add_mem U hwU (Submodule.neg_mem U hu_mem)
      rwa [sub_eq_add_neg]
    exact hw₀ hw0U
  have hdS : ∀ d : W ≃ₗ[ZMod p] W, d ∈ Δ → d S = S := by
    intro d hd
    dsimp only [S]
    rw [map_sum]
    have hbij : Function.Bijective
        (fun x : Δ => (⟨d * (x : W ≃ₗ[ZMod p] W), Δ.mul_mem hd x.2⟩ : Δ)) := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact mul_left_cancel (congrArg Subtype.val hxy)
      · intro y
        refine ⟨⟨d⁻¹ * (y : W ≃ₗ[ZMod p] W), Δ.mul_mem (Δ.inv_mem hd) y.2⟩, ?_⟩
        apply Subtype.ext
        simp only [Subtype.coe_mk]
        group
    have h := hbij.sum_comp (fun x : Δ => (x : W ≃ₗ[ZMod p] W) w₀)
    simpa [LinearEquiv.mul_apply] using h
  have hwfix : ∀ d : W ≃ₗ[ZMod p] W, d ∈ Δ → d w = w := by
    intro d hd
    dsimp only [w]
    rw [LinearEquiv.map_smul, hdS d hd]
  have hAw : ∀ a ∈ A, a w = w := by
    intro a ha
    have hfix_aw : ∀ d : W ≃ₗ[ZMod p] W, d ∈ Δ → d (a w) = a w := by
      intro d hd
      have hb : a⁻¹ * d * a ∈ Δ := by
        simpa using hΔn a⁻¹ (A.inv_mem ha) d hd
      calc d (a w) = (d * a) w := by rw [LinearEquiv.mul_apply]
        _ = (a * (a⁻¹ * d * a)) w := by
              rw [show d * a = a * (a⁻¹ * d * a) by group]
        _ = a ((a⁻¹ * d * a) w) := by rw [LinearEquiv.mul_apply]
        _ = a w := by rw [hwfix (a⁻¹ * d * a) hb]
    have hmem : a w - w ∈ U := hAU a ha w
    have hfix_diff : ∀ d : W ≃ₗ[ZMod p] W, d ∈ Δ → d (a w - w) = a w - w := by
      intro d hd
      rw [map_sub, hfix_aw d hd, hwfix d hd]
    have hzero : a w - w = 0 := hUΔ (a w - w) hmem hfix_diff
    exact sub_eq_zero.mp hzero
  exact ⟨w, hw_ne, hAw⟩

end CFSG.StandardType
