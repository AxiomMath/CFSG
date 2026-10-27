module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD9

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] noncomputable def prPL (r s : Fin 4 → k) : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  (spBil r s)⁻¹ • ((spBil.flip s).smulRight r + (spBil.flip r).smulRight s)

@[expose] noncomputable def prYL (r s : Fin 4 → k) : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  LinearMap.id - prPL r s

omit [CharP k 2] in
theorem prPL_apply (r s x : Fin 4 → k) :
    prPL r s x = (spBil x s / spBil r s) • r + (spBil x r / spBil r s) • s := by
  simp [prPL, smul_add, smul_smul, div_eq_inv_mul]

omit [CharP k 2] in
theorem prYL_apply (r s x : Fin 4 → k) : prYL r s x = x - prPL r s x :=
  rfl

theorem bil_prYL_left {r s : Fin 4 → k} (hc : spBil r s ≠ 0) (x : Fin 4 → k) :
    spBil (prYL r s x) r = 0 := by
  rw [prYL_apply, prPL_apply, LinearMap.map_sub₂, LinearMap.map_add₂, LinearMap.map_smul₂,
    LinearMap.map_smul₂, bil_self, bil_symm s r, smul_eq_mul, smul_eq_mul, mul_zero, zero_add,
    div_mul_cancel₀ _ hc, sub_self]

theorem bil_prYL_right {r s : Fin 4 → k} (hc : spBil r s ≠ 0) (x : Fin 4 → k) :
    spBil (prYL r s x) s = 0 := by
  rw [prYL_apply, prPL_apply, LinearMap.map_sub₂, LinearMap.map_add₂, LinearMap.map_smul₂,
    LinearMap.map_smul₂, bil_self, smul_eq_mul, smul_eq_mul, mul_zero, add_zero,
    div_mul_cancel₀ _ hc, sub_self]

theorem prYL_smul_add {r s : Fin 4 → k} (hc : spBil r s ≠ 0) (a b : k) :
    prYL r s (a • r + b • s) = 0 := by
  rw [prYL_apply, prPL_apply, sub_eq_zero]
  simp only [LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, bil_symm s r, smul_eq_mul,
    mul_zero, zero_add, add_zero]
  rw [mul_div_cancel_right₀ _ hc, mul_div_cancel_right₀ _ hc]

omit [CharP k 2] in
theorem prYL_of_perp {r s y : Fin 4 → k} (hyr : spBil y r = 0) (hys : spBil y s = 0) :
    prYL r s y = y := by
  rw [prYL_apply, prPL_apply, hyr, hys]
  simp

omit [CharP k 2] in
theorem form_smul_add (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) {r s : Fin 4 → k} (hr : Q r = 1)
    (hs : Q s = 1) (a b : k) : Q (a • r + b • s) = a ^ 2 + b ^ 2 + spBil r s * a * b := by
  have h := hQ (a • r) (b • s)
  rw [QuadraticMap.polar, QuadraticMap.map_smul, QuadraticMap.map_smul, hr, hs,
    LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul] at h
  linear_combination h

@[expose] noncomputable def formSt (k : Type) [Field k] : QuadraticForm k (Fin 4 → k) :=
  QuadraticMap.linMulLin (LinearMap.proj 0) (LinearMap.proj 3) +
    QuadraticMap.linMulLin (LinearMap.proj 1) (LinearMap.proj 2)

omit [CharP k 2] in
theorem formSt_apply (x : Fin 4 → k) : formSt k x = x 0 * x 3 + x 1 * x 2 := by
  simp [formSt, QuadraticMap.linMulLin_apply]

omit [CharP k 2] in
theorem polar_formSt (x y : Fin 4 → k) : QuadraticMap.polar (formSt k) x y = spBil x y := by
  simp only [QuadraticMap.polar, formSt_apply, Pi.add_apply, bil_apply]
  ring

theorem exists_linear_sq [Finite k] (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = 0) :
    ∃ ℓ : (Fin 4 → k) →ₗ[k] k, ∀ x, Q x = ℓ x ^ 2 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  choose μ hμ using fun i : Fin 4 => Refl.exists_sq_eq (Q (Pi.single i 1))
  refine ⟨∑ i, μ i • LinearMap.proj i, fun x => ?_⟩
  have hadd : ∀ a b, Q (a + b) = Q a + Q b := fun a b => by
    have h := hQ a b
    rw [QuadraticMap.polar] at h
    linear_combination h
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin 4 → k) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hQx : Q x = ∑ i, x i ^ 2 * Q (Pi.single i 1) := by
    conv_lhs => rw [hx]
    simp only [Fin.sum_univ_four, hadd, QuadraticMap.map_smul, smul_eq_mul, sq]
  rw [hQx]
  simp only [Fin.sum_univ_four, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, ← hμ]
  linear_combination (-(μ 0 * x 0 * (μ 1 * x 1 + μ 2 * x 2 + μ 3 * x 3) +
    μ 1 * x 1 * (μ 2 * x 2 + μ 3 * x 3) + μ 2 * x 2 * μ 3 * x 3)) * h2

theorem exists_form_one [Finite k] {r s : Fin 4 → k} (hc : spBil r s ≠ 0) :
    ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
      Q r = 1 ∧ Q s = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨μr, hμr⟩ := Refl.exists_sq_eq (1 + formSt k r)
  obtain ⟨μs, hμs⟩ := Refl.exists_sq_eq (1 + formSt k s)
  set ℓ : (Fin 4 → k) →ₗ[k] k :=
    (μr / spBil r s) • spBil.flip s + (μs / spBil r s) • spBil.flip r with hℓ
  have hℓr : ℓ r = μr := by
    simp [hℓ, bil_self, div_mul_cancel₀ _ hc]
  have hℓs : ℓ s = μs := by
    simp [hℓ, bil_self, bil_symm s r, div_mul_cancel₀ _ hc]
  refine ⟨formSt k + QuadraticMap.linMulLin ℓ ℓ, fun x y => ?_, ?_, ?_⟩
  · rw [FunLike.coe_add, QuadraticMap.polar_add, polar_formSt]
    have h0 : QuadraticMap.polar (QuadraticMap.linMulLin ℓ ℓ) x y = 0 := by
      simp only [QuadraticMap.polar, QuadraticMap.linMulLin_apply, map_add]
      linear_combination (ℓ x * ℓ y) * h2
    rw [h0, add_zero]
  · rw [add_apply, QuadraticMap.linMulLin_apply, hℓr, ← sq, hμr]
    linear_combination formSt k r * h2
  · rw [add_apply, QuadraticMap.linMulLin_apply, hℓs, ← sq, hμs]
    linear_combination formSt k s * h2

theorem exists_eq_add_smul {r s y x : Fin 4 → k} (hc : spBil r s ≠ 0) (hy : y ≠ 0)
    (hyr : spBil y r = 0) (hys : spBil y s = 0) (hx : spBil x y = 0) :
    ∃ α β γ : k, x = α • r + β • s + γ • y := by
  obtain ⟨σ, hσ⟩ := exists_act_eOne hy
  have hr2 : natAct σ⁻¹ r 2 = 0 := by rw [inv_act_two hσ, bil_symm, hyr]
  have hs2 : natAct σ⁻¹ s 2 = 0 := by rw [inv_act_two hσ, bil_symm, hys]
  have hx2 : natAct σ⁻¹ x 2 = 0 := by rw [inv_act_two hσ, hx]
  have hw2 : ((spBil r s)⁻¹ • natAct σ⁻¹ s) 2 = 0 := by simp [hs2]
  have hvw : spBil (natAct σ⁻¹ r) ((spBil r s)⁻¹ • natAct σ⁻¹ s) = 1 := by
    rw [map_smul, smul_eq_mul, bil_act, inv_mul_cancel₀ hc]
  have hd := eq_frame_add hr2 hw2 hx2 hvw
  refine ⟨spBil ((spBil r s)⁻¹ • natAct σ⁻¹ s) (natAct σ⁻¹ x),
    spBil (natAct σ⁻¹ r) (natAct σ⁻¹ x) * (spBil r s)⁻¹,
    natAct σ⁻¹ x 1 - spBil ((spBil r s)⁻¹ • natAct σ⁻¹ s) (natAct σ⁻¹ x) * natAct σ⁻¹ r 1 -
      spBil (natAct σ⁻¹ r) (natAct σ⁻¹ x) * ((spBil r s)⁻¹ • natAct σ⁻¹ s) 1, ?_⟩
  apply act_injective σ⁻¹
  rw [act_add, act_add, act_smul, act_smul, act_smul, ← hσ, act_inv_act]
  conv_lhs => rw [hd]
  rw [smul_smul]

theorem exists_perp_ne_zero {r s : Fin 4 → k} (hc : spBil r s ≠ 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ spBil y r = 0 ∧ spBil y s = 0 := by
  classical
  have hne : Submodule.span k (({r, s} : Finset (Fin 4 → k)) : Set (Fin 4 → k)) ≠ ⊤ := by
    intro h
    have h1 : Module.finrank k (Submodule.span k (({r, s} : Finset (Fin 4 → k)) :
        Set (Fin 4 → k))) ≤ 2 :=
      (finrank_span_finset_le_card (R := k) ({r, s} : Finset (Fin 4 → k))).trans
        Finset.card_le_two
    rw [h, finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  refine ⟨prYL r s v, fun h0 => hv ?_, bil_prYL_left hc v, bil_prYL_right hc v⟩
  have hv' : v = prPL r s v := by
    rw [prYL_apply, sub_eq_zero] at h0
    exact h0
  rw [hv', prPL_apply]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end CFSG.Quasithin.Ch3E213M.G41.Big
