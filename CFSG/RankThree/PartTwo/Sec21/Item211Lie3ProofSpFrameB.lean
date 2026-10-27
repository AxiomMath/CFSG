module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpXi
public import CFSG.RankThree.SubgroupLists.TransvectionRecognition
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie3Proof

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.RankThree.SubgroupLists (spForm spGram spForm_eq_dotProduct spForm_self
  eq_zero_of_forall_spForm spForm_swap)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

section Frame

variable {j₀ : Matrix V₄ V₄ K}
  (hskew : ∀ x y, spForm 2 K (j₀ *ᵥ x) y = -spForm 2 K x (j₀ *ᵥ y))
  (hsq : ∀ x, j₀ *ᵥ (j₀ *ᵥ x) = -(3 : K) • x)

include hskew in
theorem spForm_mulVec_symm (v w : V₄ → K) :
    spForm 2 K w (j₀ *ᵥ v) = spForm 2 K v (j₀ *ᵥ w) := by
  rw [spForm_swap, hskew, neg_neg]

@[expose] def comb (j₀ : Matrix V₄ V₄ K) (u u' : V₄ → K) (x₁ x₂ x₃ x₄ : K) : V₄ → K :=
  x₁ • u + x₂ • (j₀ *ᵥ u) + x₃ • u' + x₄ • (j₀ *ᵥ u')

include hsq in
theorem mulVec_comb (u u' : V₄ → K) (x₁ x₂ x₃ x₄ : K) :
    j₀ *ᵥ comb j₀ u u' x₁ x₂ x₃ x₄ = comb j₀ u u' (-3 * x₂) x₁ (-3 * x₄) x₃ := by
  simp only [comb, Matrix.mulVec_add, Matrix.mulVec_smul, hsq, smul_smul]
  module

include hskew hsq in
theorem spForm_comb {u u' : V₄ → K} (h1 : spForm 2 K u u' = 0)
    (h2 : spForm 2 K (j₀ *ᵥ u) u' = 0) (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : K) :
    spForm 2 K (comb j₀ u u' x₁ x₂ x₃ x₄) (comb j₀ u u' y₁ y₂ y₃ y₄) =
      spForm 2 K u (j₀ *ᵥ u) * (x₁ * y₂ - x₂ * y₁) +
        spForm 2 K u' (j₀ *ᵥ u') * (x₃ * y₄ - x₄ * y₃) := by
  have a1 : spForm 2 K u' u = 0 := by rw [spForm_swap, h1, neg_zero]
  have a2 : spForm 2 K u' (j₀ *ᵥ u) = 0 := by rw [spForm_swap, h2, neg_zero]
  have a3 : spForm 2 K u (j₀ *ᵥ u') = 0 := by
    rw [← spForm_mulVec_symm hskew, spForm_swap, h2, neg_zero]
  have a4 : spForm 2 K (j₀ *ᵥ u') u = 0 := by rw [spForm_swap, a3, neg_zero]
  have a5 : spForm 2 K (j₀ *ᵥ u) (j₀ *ᵥ u') = 0 := by
    rw [hskew, hsq, map_smul, h1, smul_zero, neg_zero]
  have a6 : spForm 2 K (j₀ *ᵥ u') (j₀ *ᵥ u) = 0 := by rw [spForm_swap, a5, neg_zero]
  have a7 : spForm 2 K (j₀ *ᵥ u) u = -spForm 2 K u (j₀ *ᵥ u) := spForm_swap _ _
  have a8 : spForm 2 K (j₀ *ᵥ u') u' = -spForm 2 K u' (j₀ *ᵥ u') := spForm_swap _ _
  simp only [comb, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    spForm_self, h1, h2, a1, a2, a3, a4, a5, a6, a7, a8]
  ring

end Frame

theorem card_odd_of_two_ne_zero [Fintype K] (h2 : (2 : K) ≠ 0) : Fintype.card K % 2 = 1 := by
  apply FiniteField.odd_card_of_char_ne_two
  intro h
  apply h2
  have e := ringChar.Nat.cast_ringChar (R := K)
  rw [h] at e
  exact_mod_cast e

theorem exists_frame_free [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {j₀ : Matrix V₄ V₄ K}
    (hskew : ∀ x y, spForm 2 K (j₀ *ᵥ x) y = -spForm 2 K x (j₀ *ᵥ y))
    (hsq : ∀ x, j₀ *ᵥ (j₀ *ᵥ x) = -(3 : K) • x) :
    ∃ h : GL V₄ K, h ∈ StatedSp 2 K ∧ j₀ * (h : Matrix V₄ V₄ K) = (h : Matrix V₄ V₄ K) * jStd := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set Q : (V₄ → K) → K := fun v => spForm 2 K v (j₀ *ᵥ v) with hQ
  have hQadd : ∀ v w, Q (v + w) = Q v + Q w + 2 * spForm 2 K v (j₀ *ᵥ w) := by
    intro v w
    simp only [hQ, Matrix.mulVec_add, map_add, LinearMap.add_apply]
    rw [spForm_mulVec_symm hskew v w]
    ring
  obtain ⟨u, hu⟩ : ∃ u, Q u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ v w, spForm 2 K v (j₀ *ᵥ w) = 0 := by
      intro v w
      have e := hQadd v w
      rw [hcon, hcon, hcon] at e
      have e' : (2 : K) * spForm 2 K v (j₀ *ᵥ w) = 0 := by linear_combination -e
      exact (mul_eq_zero.mp e').resolve_left h2
    have hj : ∀ w, j₀ *ᵥ w = 0 := fun w => eq_zero_of_forall_spForm fun x => hz x w
    have e := hsq (Pi.single (Sum.inl 0) 1)
    rw [hj] at e
    have e2 := congrFun e (Sum.inl 0)
    simp at e2
    exact h3 e2
  set c := Q u with hc
  obtain ⟨u', hu'1, hu'2, hu'⟩ : ∃ u', spForm 2 K u u' = 0 ∧ spForm 2 K (j₀ *ᵥ u) u' = 0 ∧
      Q u' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    set f : (V₄ → K) →ₗ[K] K × K := (spForm 2 K u).prod (spForm 2 K (j₀ *ᵥ u)) with hf
    have hlt : Module.finrank K (K × K) < Module.finrank K (V₄ → K) := by
      rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card]
      simp
    obtain ⟨w, hw, hw0⟩ :=
      (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
    have hw' := LinearMap.mem_ker.mp hw
    have hw1 : spForm 2 K u w = 0 := by
      have e := congrArg Prod.fst hw'
      simpa [hf] using e
    have hw2 : spForm 2 K (j₀ *ᵥ u) w = 0 := by
      have e := congrArg Prod.snd hw'
      simpa [hf] using e
    have hjw1 : spForm 2 K u (j₀ *ᵥ w) = 0 := by
      rw [← neg_eq_zero, ← hskew, hw2]
    have hjw2 : spForm 2 K (j₀ *ᵥ u) (j₀ *ᵥ w) = 0 := by
      rw [hskew, hsq, map_smul, hw1, smul_zero, neg_zero]
    have hperp : ∀ x, spForm 2 K u x = 0 → spForm 2 K (j₀ *ᵥ u) x = 0 →
        spForm 2 K x (j₀ *ᵥ w) = 0 := by
      intro x hx1 hx2
      have e := hQadd x w
      rw [hcon (x + w) (by rw [map_add, hx1, hw1, add_zero])
        (by rw [map_add, hx2, hw2, add_zero]), hcon x hx1 hx2, hcon w hw1 hw2] at e
      have e' : (2 : K) * spForm 2 K x (j₀ *ᵥ w) = 0 := by linear_combination -e
      exact (mul_eq_zero.mp e').resolve_left h2
    have hjw : j₀ *ᵥ w = 0 := by
      apply eq_zero_of_forall_spForm
      intro x
      have hcB : spForm 2 K u (j₀ *ᵥ u) = c := rfl
      have hcu : spForm 2 K (j₀ *ᵥ u) u = -c := by rw [spForm_swap, hcB]
      set β := spForm 2 K u x / c with hβ
      set α := -(spForm 2 K (j₀ *ᵥ u) x) / c with hα
      have hβc : β * c = spForm 2 K u x := by rw [hβ, div_mul_cancel₀ _ hu]
      have hαc : α * c = -(spForm 2 K (j₀ *ᵥ u) x) := by rw [hα, div_mul_cancel₀ _ hu]
      set x' := x - α • u - β • (j₀ *ᵥ u) with hx'
      have hx'1 : spForm 2 K u x' = 0 := by
        rw [hx', map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, spForm_self,
          hcB]
        linear_combination -hβc
      have hx'2 : spForm 2 K (j₀ *ᵥ u) x' = 0 := by
        rw [hx', map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, spForm_self,
          hcu]
        linear_combination hαc
      have hxx : x = x' + α • u + β • (j₀ *ᵥ u) := by rw [hx']; abel
      rw [hxx, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_smul, map_smul,
        LinearMap.smul_apply, LinearMap.smul_apply, hperp x' hx'1 hx'2, hjw1, hjw2, smul_zero,
        smul_zero, add_zero, add_zero]
    apply hw0
    have e := hsq w
    rw [hjw, Matrix.mulVec_zero] at e
    have e' : (-(3 : K)) • w = 0 := e.symm
    exact (smul_eq_zero.mp e').resolve_left (neg_ne_zero.mpr h3)
  set c' := Q u' with hc'
  obtain ⟨α, β, hαβ⟩ : ∃ α β : K, c * α ^ 2 + c' + 3 * c * β ^ 2 = 0 := by
    have hf := Polynomial.degree_quadratic (a := c) (b := 0) (c := c') hu
    have hg := Polynomial.degree_quadratic (a := 3 * c) (b := 0) (c := 0) (mul_ne_zero h3 hu)
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg (card_odd_of_two_ne_zero h2)
    refine ⟨a, b, ?_⟩
    simpa using hab
  have hc'0 : c' ≠ 0 := hu'
  obtain ⟨κ, hκ⟩ : ∃ κ : K, c' * κ = 1 := ⟨c'⁻¹, mul_inv_cancel₀ hc'0⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : K, 2 * c' * γ = -1 := ⟨-(2 * c')⁻¹, by
    rw [mul_neg, mul_inv_cancel₀ (mul_ne_zero h2 hc'0)]⟩
  set v₁ := comb j₀ u u' α β 1 0 with hv₁
  set v₂ := comb j₀ u u' (-3 * β * γ) (α * γ) 0 (κ + γ) with hv₂
  have hjv₁ : j₀ *ᵥ v₁ = comb j₀ u u' (-3 * β) α (-3 * 0) 1 := mulVec_comb hsq _ _ _ _ _ _
  have hjv₂ : j₀ *ᵥ v₂ = comb j₀ u u' (-3 * (α * γ)) (-3 * β * γ) (-3 * (κ + γ)) 0 :=
    mulVec_comb hsq _ _ _ _ _ _
  have hB := spForm_comb hskew hsq hu'1 hu'2
  have hcB : spForm 2 K u (j₀ *ᵥ u) = c := rfl
  have hc'B : spForm 2 K u' (j₀ *ᵥ u') = c' := rfl
  have g12 : spForm 2 K v₁ (j₀ *ᵥ v₁) = 0 := by
    rw [hjv₁, hv₁, hB, hcB, hc'B]
    linear_combination hαβ
  have g13 : spForm 2 K v₁ v₂ = 1 := by
    rw [hv₁, hv₂, hB, hcB, hc'B]
    linear_combination γ * hαβ + hκ
  have g14 : spForm 2 K v₁ (j₀ *ᵥ v₂) = 0 := by
    rw [hjv₂, hv₁, hB]
    ring
  have g23 : spForm 2 K (j₀ *ᵥ v₁) v₂ = 0 := by
    rw [hjv₁, hv₂, hB]
    ring
  have g24 : spForm 2 K (j₀ *ᵥ v₁) (j₀ *ᵥ v₂) = 3 := by
    rw [hjv₁, hjv₂, hB, hcB, hc'B]
    linear_combination 3 * γ * hαβ + 3 * hκ
  have g34 : spForm 2 K v₂ (j₀ *ᵥ v₂) = 0 := by
    rw [hjv₂, hv₂, hB, hcB, hc'B]
    linear_combination 3 * γ ^ 2 * hαβ + 3 * κ * hκ + 3 * κ * hγ
  have g21 : spForm 2 K (j₀ *ᵥ v₁) v₁ = 0 := by rw [spForm_swap, g12, neg_zero]
  have g31 : spForm 2 K v₂ v₁ = -1 := by rw [spForm_swap, g13]
  have g41 : spForm 2 K (j₀ *ᵥ v₂) v₁ = 0 := by rw [spForm_swap, g14, neg_zero]
  have g32 : spForm 2 K v₂ (j₀ *ᵥ v₁) = 0 := by rw [spForm_swap, g23, neg_zero]
  have g42 : spForm 2 K (j₀ *ᵥ v₂) (j₀ *ᵥ v₁) = -3 := by rw [spForm_swap, g24]
  have g43 : spForm 2 K (j₀ *ᵥ v₂) v₂ = 0 := by rw [spForm_swap, g34, neg_zero]
  set col : V₄ → (V₄ → K) := Sum.elim ![v₁, j₀ *ᵥ v₁] ![v₂, (3 : K)⁻¹ • (j₀ *ᵥ v₂)] with hcol_def
  set H : Matrix V₄ V₄ K := Matrix.of fun i k => col k i with hH
  have hcol : ∀ k, H *ᵥ Pi.single k 1 = col k := by
    intro k
    ext i
    simp [hH, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hgram : Hᵀ * spGram 2 K * H = spGram 2 K := by
    have key : ∀ a b, (Hᵀ * spGram 2 K * H) a b = spForm 2 K (col a) (col b) := by
      intro a b
      rw [spForm_eq_dotProduct]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, hH,
        Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have h33 : (3 : K)⁻¹ * 3 = 1 := inv_mul_cancel₀ h3
    ext a b
    rw [key]
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [hcol_def, map_smul, spForm_self, g12, g13, g14, g23, g24, g34, g21, g31, g41, g32,
        g42, g43, spGram, Matrix.fromBlocks, h33]
  have hs : ∀ (l : V₄) (a : K), H *ᵥ (a • Pi.single l 1) = a • col l := fun l a => by
    rw [Matrix.mulVec_smul, hcol]
  have ej1 : (jStd : Matrix V₄ V₄ K) *ᵥ Pi.single (Sum.inl 0) 1 =
      (1 : K) • Pi.single (Sum.inl 1) 1 := by
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [jStd, xiMat, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Pi.single_apply]
  have ej2 : (jStd : Matrix V₄ V₄ K) *ᵥ Pi.single (Sum.inl 1) 1 =
      (-3 : K) • Pi.single (Sum.inl 0) 1 := by
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [jStd, xiMat, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Pi.single_apply]
  have ej3 : (jStd : Matrix V₄ V₄ K) *ᵥ Pi.single (Sum.inr 0) 1 =
      (3 : K) • Pi.single (Sum.inr 1) 1 := by
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [jStd, xiMat, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Pi.single_apply]
  have ej4 : (jStd : Matrix V₄ V₄ K) *ᵥ Pi.single (Sum.inr 1) 1 =
      (-1 : K) • Pi.single (Sum.inr 0) 1 := by
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [jStd, xiMat, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Pi.single_apply]
  have k1 : j₀ *ᵥ col (Sum.inl 0) = H *ᵥ (jStd *ᵥ Pi.single (Sum.inl 0) 1) := by
    rw [ej1, hs, one_smul]
    simp [hcol_def]
  have k2 : j₀ *ᵥ col (Sum.inl 1) = H *ᵥ (jStd *ᵥ Pi.single (Sum.inl 1) 1) := by
    rw [ej2, hs]
    simp [hcol_def, hsq]
  have k3 : j₀ *ᵥ col (Sum.inr 0) = H *ᵥ (jStd *ᵥ Pi.single (Sum.inr 0) 1) := by
    rw [ej3, hs]
    simp [hcol_def, smul_smul, mul_inv_cancel₀ h3]
  have k4 : j₀ *ᵥ col (Sum.inr 1) = H *ᵥ (jStd *ᵥ Pi.single (Sum.inr 1) 1) := by
    rw [ej4, hs]
    have e : (3 : K)⁻¹ • (-(3 : K) • v₂) = (-1 : K) • v₂ := by
      rw [smul_smul, mul_neg, inv_mul_cancel₀ h3]
    simpa [hcol_def, Matrix.mulVec_smul, hsq] using e
  set Hinv : Matrix V₄ V₄ K := -(spGram 2 K * Hᵀ * spGram 2 K) with hHinv
  have hinvH : Hinv * H = 1 := by
    rw [hHinv, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ, hgram,
      spGram_mul_self, neg_neg]
  have hHinv' : H * Hinv = 1 := mul_eq_one_comm.mp hinvH
  refine ⟨⟨H, Hinv, hHinv', hinvH⟩, ?_, ?_⟩
  · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    exact hgram
  · show j₀ * H = H * jStd
    refine Matrix.ext_of_mulVec_single fun k => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
    rcases k with k | k <;> fin_cases k
    · exact k1
    · exact k2
    · exact k3
    · exact k4

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
