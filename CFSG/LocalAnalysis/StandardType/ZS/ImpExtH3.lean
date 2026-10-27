module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtTable
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

structure FourThreeData (f : Module.Basis (Fin 4) (ZMod p) U) (lam : (ZMod p)ˣ)
    (a₁ a₂ a₃ a₄ : U ≃ₗ[ZMod p] U) (K F : Subgroup (U ≃ₗ[ZMod p] U)) : Prop where
  orderOf_lam : orderOf lam = 5
  toMatrix_a₁ : LinearMap.toMatrix f f a₁.toLinearMap = pijMat 0 1 1
  toMatrix_a₂ : LinearMap.toMatrix f f a₂.toLinearMap = pijMat 0 1 (lam : ZMod p)
  toMatrix_a₃ : LinearMap.toMatrix f f a₃.toLinearMap = pijMat 1 2 1
  isRefl_a₄ : IsRefl p a₄
  eq_K : K = Subgroup.closure {a₁, a₂, a₃} ⊔ F
  irred : ∀ W : Submodule (ZMod p) U, (∀ k ∈ K, ∀ w ∈ W, k w ∈ W) → W = ⊥ ∨ W = ⊤
  transvectionFree : QTwoLin.TransvectionFree K
  dmax : DMax p K 5
  a₁_mem : a₁ ∈ F
  a₂_mem : a₂ ∈ F
  a₄_mem : a₄ ∈ F
  splitSupport_F : SplitSupport F 3
  h3 : H3Data p (movedGroup F)
  splitOfIrred : SplitOfIrred p K 3
  noOrth : ∀ X ≤ K, ReflGen p X → SplitSupport X 3 →
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) →
    (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    ¬ IsOrthType p (movedGroup X)
  negOfPrim : TFNegOfPrimThree p

private lemma zs4h_pij01_mul_apply (α : ZMod p) (M : Matrix (Fin 4) (Fin 4) (ZMod p)) (j : Fin 4) :
    (pijMat (0 : Fin 4) (1 : Fin 4) α * M) 0 j = α * M 1 j ∧
      (pijMat (0 : Fin 4) (1 : Fin 4) α * M) 1 j = α⁻¹ * M 0 j ∧
      (pijMat (0 : Fin 4) (1 : Fin 4) α * M) 2 j = M 2 j ∧
      (pijMat (0 : Fin 4) (1 : Fin 4) α * M) 3 j = M 3 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four, pijMat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

private lemma zs4h_mul_pij01_apply (α : ZMod p) (M : Matrix (Fin 4) (Fin 4) (ZMod p)) (i : Fin 4) :
    (M * pijMat (0 : Fin 4) (1 : Fin 4) α) i 0 = α⁻¹ * M i 1 ∧
      (M * pijMat (0 : Fin 4) (1 : Fin 4) α) i 1 = α * M i 0 ∧
      (M * pijMat (0 : Fin 4) (1 : Fin 4) α) i 2 = M i 2 ∧
      (M * pijMat (0 : Fin 4) (1 : Fin 4) α) i 3 = M i 3 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four, pijMat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mul_comm]

private lemma zs4h_shape_entries1 {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hc : pijMat (0 : Fin 4) (1 : Fin 4) (1 : ZMod p) * M = M * pijMat 0 1 1) :
    M 1 1 = M 0 0 ∧ M 1 0 = M 0 1 ∧ M 1 2 = M 0 2 ∧ M 1 3 = M 0 3 ∧
      M 2 1 = M 2 0 ∧ M 3 1 = M 3 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (have := congrFun (congrFun hc 0) 1
       simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this)
    | (have := congrFun (congrFun hc 0) 0
       simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this)
    | (have := congrFun (congrFun hc 0) 2
       simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this)
    | (have := congrFun (congrFun hc 0) 3
       simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this)
    | (have := congrFun (congrFun hc 2) 1
       simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this)
    | (have := congrFun (congrFun hc 3) 1
       simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this)

private lemma zs4h_shape_entries2 {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hc : pijMat (2 : Fin 4) (3 : Fin 4) (1 : ZMod p) * M = M * pijMat 2 3 1)
    (h21 : M 2 1 = M 2 0) :
    M 0 3 = M 0 2 ∧ M 1 3 = M 1 2 ∧ M 3 0 = M 2 0 ∧ M 3 1 = M 2 0 ∧
      M 3 3 = M 2 2 ∧ M 3 2 = M 2 3 := by
  have e03 : M 0 2 = M 0 3 := by
    have := congrFun (congrFun hc 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this
  have e13 : M 1 2 = M 1 3 := by
    have := congrFun (congrFun hc 1) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this
  have e30 : M 3 0 = M 2 0 := by
    have := congrFun (congrFun hc 2) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this
  have e31 : M 3 1 = M 2 1 := by
    have := congrFun (congrFun hc 2) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this
  have e33 : M 3 3 = M 2 2 := by
    have := congrFun (congrFun hc 2) 3
    simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this
  have e32 : M 3 2 = M 2 3 := by
    have := congrFun (congrFun hc 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_four, pijMat] using this
  exact ⟨e03.symm, e13.symm, e30, e31.trans h21, e33, e32⟩

private theorem zs4h_shape {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) {a₁ z a₄ : U ≃ₗ[ZMod p] U}
    (ha₁ : LinearMap.toMatrix f f a₁.toLinearMap = pijMat 0 1 1)
    (hz : LinearMap.toMatrix f f z.toLinearMap = -pijMat 2 3 1)
    (h₁ : a₁ * a₄ = a₄ * a₁) (hz₄ : z * a₄ = a₄ * z) :
    LinearMap.toMatrix f f a₄.toLinearMap =
      !![LinearMap.toMatrix f f a₄.toLinearMap 0 0, LinearMap.toMatrix f f a₄.toLinearMap 0 1,
          LinearMap.toMatrix f f a₄.toLinearMap 0 2, LinearMap.toMatrix f f a₄.toLinearMap 0 2;
        LinearMap.toMatrix f f a₄.toLinearMap 0 1, LinearMap.toMatrix f f a₄.toLinearMap 0 0,
          LinearMap.toMatrix f f a₄.toLinearMap 0 2, LinearMap.toMatrix f f a₄.toLinearMap 0 2;
        LinearMap.toMatrix f f a₄.toLinearMap 2 0, LinearMap.toMatrix f f a₄.toLinearMap 2 0,
          LinearMap.toMatrix f f a₄.toLinearMap 2 2, LinearMap.toMatrix f f a₄.toLinearMap 2 3;
        LinearMap.toMatrix f f a₄.toLinearMap 2 0, LinearMap.toMatrix f f a₄.toLinearMap 2 0,
          LinearMap.toMatrix f f a₄.toLinearMap 2 3,
          LinearMap.toMatrix f f a₄.toLinearMap 2 2] := by
  set M := LinearMap.toMatrix f f a₄.toLinearMap with hM
  have hcomm1 : pijMat 0 1 (1 : ZMod p) * M = M * pijMat 0 1 (1 : ZMod p) := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap) h₁
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul] at h
    rw [ha₁] at h
    exact h
  have hcomm2 : pijMat 2 3 (1 : ZMod p) * M = M * pijMat 2 3 (1 : ZMod p) := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap) hz₄
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul] at h
    rw [hz] at h
    rw [neg_mul, mul_neg] at h
    exact neg_injective h
  obtain ⟨h11, h10, h12, h13, h21, h31⟩ := zs4h_shape_entries1 hcomm1
  obtain ⟨h03, h13', h30, h31', h33, h32⟩ := zs4h_shape_entries2 hcomm2 h21
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, h11, h10, h12, h13, h21,
      h31, h03, h30, h33, h32]

private lemma zs4h_N_lit {a b pp r c d l : ZMod p} :
    pijMat (0 : Fin 4) (1 : Fin 4) l * !![a, b, pp, pp; b, a, pp, pp; r, r, c, d; r, r, d, c] =
      !![l * b, l * a, l * pp, l * pp; l⁻¹ * a, l⁻¹ * b, l⁻¹ * pp, l⁻¹ * pp;
        r, r, c, d; r, r, d, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, pijMat]

private lemma zs4h_MP_lit {a b pp r c d l : ZMod p} :
    !![a, b, pp, pp; b, a, pp, pp; r, r, c, d; r, r, d, c] * pijMat (0 : Fin 4) (1 : Fin 4) l =
      !![l⁻¹ * b, l * a, pp, pp; l⁻¹ * a, l * b, pp, pp; l⁻¹ * r, l * r, c, d;
        l⁻¹ * r, l * r, d, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, mul_comm]

private lemma zs4h_F_facts {a b pp r c d l : ZMod p} (hl0 : l ≠ 0)
    (hN2 : (pijMat (0 : Fin 4) (1 : Fin 4) l *
        !![a, b, pp, pp; b, a, pp, pp; r, r, c, d; r, r, d, c]) ^ 2 =
      !![a, b, pp, pp; b, a, pp, pp; r, r, c, d; r, r, d, c] * pijMat (0 : Fin 4) (1 : Fin 4) l) :
    r * (l * b + l⁻¹ * a + c + d) = l⁻¹ * r ∧ r * (l * a + l⁻¹ * b + c + d) = l * r ∧
      r * ((l + l⁻¹) * pp) + c * c + d * d = c ∧ r * ((l + l⁻¹) * pp) + 2 * c * d = d ∧
      l ^ 2 * b * b + a * a + 2 * l * pp * r = l⁻¹ * b := by
  rw [zs4h_N_lit, zs4h_MP_lit, pow_two] at hN2
  have hinv : l * l⁻¹ = 1 := mul_inv_cancel₀ hl0
  have h20 := congrFun (congrFun hN2 2) 0
  have h21 := congrFun (congrFun hN2 2) 1
  have h22 := congrFun (congrFun hN2 2) 2
  have h23 := congrFun (congrFun hN2 2) 3
  have h00 := congrFun (congrFun hN2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four] at h20 h21 h22 h23 h00
  exact ⟨by linear_combination h20, by linear_combination h21, by linear_combination h22,
    by linear_combination h23, by linear_combination h00 - a ^ 2 * hinv⟩

private lemma zs4h_E_facts {a b pp r c d : ZMod p} (h2ne : (2 : ZMod p) ≠ 0)
    (hmul : (!![a, b, pp, pp; b, a, pp, pp; r, r, c, d; r, r, d, c] :
        Matrix (Fin 4) (Fin 4) (ZMod p)) *
      !![a, b, pp, pp; b, a, pp, pp; r, r, c, d; r, r, d, c] = 1) :
    a * a + b * b + 2 * pp * r = 1 ∧ a * b + pp * r = 0 ∧ c * c + d * d + 2 * pp * r = 1 ∧
      c * d + pp * r = 0 := by
  have h00 := congrFun (congrFun hmul 0) 0
  have h01 := congrFun (congrFun hmul 0) 1
  have h22 := congrFun (congrFun hmul 2) 2
  have h23 := congrFun (congrFun hmul 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at h00 h01 h22 h23
  refine ⟨by linear_combination h00, ?_, by linear_combination h22, ?_⟩
  · have h : (2 : ZMod p) * (a * b + pp * r) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp h).resolve_left h2ne
  · have h : (2 : ZMod p) * (c * d + pp * r) = 0 := by linear_combination h23
    exact (mul_eq_zero.mp h).resolve_left h2ne

private lemma zs4h_alg_r0 {a b pp r l m : ZMod p} (hr : r = 0) (hlm : l * m = 1)
    (hl6 : l ^ 6 ≠ 1) (F5 : l ^ 2 * b * b + a * a + 2 * l * pp * r = m * b)
    (E1 : a * a + b * b + 2 * pp * r = 1) (E2 : a * b + pp * r = 0) : False := by
  have hab : a * b = 0 := by linear_combination (norm := ring_nf) E2 - pp * hr
  have hE1 := E1; rw [hr] at hE1; simp only [mul_zero, add_zero] at hE1
  have hF5 := F5; rw [hr] at hF5; simp only [mul_zero, add_zero] at hF5
  rcases mul_eq_zero.mp hab with ha0 | hb0
  · have hb2 : b * b = 1 := by
      have h := hE1; rw [ha0] at h; simp only [mul_zero, zero_add] at h; exact h
    have hF5' : l ^ 2 = m * b := by
      have h := hF5
      rw [ha0, mul_zero, add_zero] at h
      rw [mul_assoc, hb2, mul_one] at h
      exact h
    have hb3 : l ^ 3 = b := by linear_combination (norm := ring_nf) l * hF5' + b * hlm
    have h6 : l ^ 6 = 1 := by
      rw [← hb3] at hb2
      linear_combination (norm := ring_nf) hb2
    exact hl6 h6
  · have ha2 : a * a = 1 := by
      have h := hE1; rw [hb0] at h; simp only [mul_zero, add_zero] at h; exact h
    have ha0' : a * a = 0 := by
      have h := hF5; rw [hb0] at h; simp only [mul_zero, zero_add] at h; exact h
    exact one_ne_zero (by linear_combination (norm := ring_nf) ha0' - ha2 : (1 : ZMod p) = 0)

private lemma zs4h_alg_L {l m : ZMod p} (hlm : l * m = 1) (hl4 : l ^ 4 ≠ 1) : l + m ≠ 0 := by
  intro hh
  have hm_eq : m = -l := by linear_combination (norm := ring_nf) hh
  have h2 : l * l = -1 := by linear_combination (norm := ring_nf) l * hm_eq - hlm
  exact hl4 (by linear_combination (norm := ring_nf) (l ^ 2) * h2 - h2)

private lemma zs4h_alg_s2 {l m : ZMod p} (hlm : l * m = 1) (hl1 : l ≠ 1) :
    (l + m) - 2 ≠ 0 := by
  intro hh
  have h1 : (l - 1) ^ 2 = 0 := by linear_combination (norm := ring_nf) l * hh - hlm
  rw [pow_two] at h1
  exact hl1 (sub_eq_zero.mp (mul_self_eq_zero.mp h1))

private lemma zs4h_alg_r1 {a b c d pp r l m : ZMod p} (hr : r ≠ 0) (hne0 : l - m ≠ 0)
    (F1 : r * (l * b + m * a + c + d) = m * r) (F2 : r * (l * a + m * b + c + d) = l * r)
    (E2 : a * b + pp * r = 0) (E4 : c * d + pp * r = 0) :
    b = a - 1 ∧ pp * r = -a * (a - 1) ∧ c * d = a * (a - 1) ∧ c + d = (l + m) * (1 - a) := by
  have hdiff : r * (l - m) * (b - a + 1) = 0 := by linear_combination (norm := ring_nf) F1 - F2
  have hb : b = a - 1 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact absurd h (mul_ne_zero hr hne0)
    · linear_combination h
  have hpr : pp * r = -a * (a - 1) := by linear_combination (norm := ring_nf) E2 - a * hb
  have hcd : c * d = a * (a - 1) := by linear_combination (norm := ring_nf) E4 - hpr
  have hsum' : r * (c + d - (l + m) * (1 - a)) = 0 := by
    linear_combination (norm := ring_nf) F1 - l * r * hb
  refine ⟨hb, hpr, hcd, ?_⟩
  have h := (mul_eq_zero.mp hsum').resolve_left hr
  linear_combination (norm := ring_nf) h

private lemma zs4h_alg_hu {a b c d pp r l m : ZMod p} (hL : l + m ≠ 0) (hb : b = a - 1)
    (F3 : r * ((l + m) * pp) + c * c + d * d = c) (F4 : r * ((l + m) * pp) + 2 * c * d = d)
    (E2 : a * b + pp * r = 0) (E3 : c * c + d * d + 2 * pp * r = 1)
    (hpr : pp * r = -a * (a - 1)) (hcd : c * d = a * (a - 1))
    (hsum : c + d = (l + m) * (1 - a)) : ((l + m) - 2) * (1 - a) + 1 = 0 := by
  have hsq : (c + d) ^ 2 = c + d + 2 * (l + m) * (a * (a - 1)) := by
    linear_combination (norm := ring_nf) F3 + F4 - 2 * (l + m) * hpr
  have hLhu : (l + m) * ((1 - a) * (((l + m) - 2) * (1 - a) + 1)) = 0 := by
    linear_combination (norm := ring_nf) hsq - ((c + d) + (l + m) * (1 - a) - 1) * hsum
  have hu : (1 - a) * (((l + m) - 2) * (1 - a) + 1) = 0 :=
    (mul_eq_zero.mp hLhu).resolve_left hL
  have ha1 : a ≠ 1 := by
    intro ha1
    have hb0 : b = 0 := by linear_combination (norm := ring_nf) hb + ha1
    have hcd0 : c * d = 0 := by linear_combination (norm := ring_nf) hcd - a * hb + a * hb0
    have hsum0 : c + d = 0 := by linear_combination (norm := ring_nf) hsum - (l + m) * ha1
    have hpr0 : pp * r = 0 := by linear_combination (norm := ring_nf) E2 - a * hb0
    have hcc : c * c + d * d = 1 := by linear_combination (norm := ring_nf) E3 - 2 * hpr0
    have h2 : (c + d) ^ 2 = 1 := by linear_combination (norm := ring_nf) hcc + 2 * hcd0
    rw [hsum0] at h2
    norm_num at h2
  rcases mul_eq_zero.mp hu with h | h
  · exact absurd (sub_eq_zero.mp h).symm ha1
  · exact h

private lemma zs4h_alg_cd {a c d pp r l m : ZMod p}
    (F3 : r * ((l + m) * pp) + c * c + d * d = c) (hpr : pp * r = -a * (a - 1))
    (hcd : c * d = a * (a - 1)) (hsum : c + d = (l + m) * (1 - a))
    (hu1 : ((l + m) - 2) * (1 - a) + 1 = 0) : c = 1 - a ∧ d = -a := by
  have hcW : c = ((l + m) ^ 2) * (1 - a) ^ 2 - ((l + m) + 2) * (a * (a - 1)) := by
    linear_combination (norm := ring_nf)
      (-(1 : ZMod p)) * F3 + (l + m) * hpr
      + ((c + d) + (l + m) * (1 - a)) * hsum + (-2 : ZMod p) * hcd
  have hc : c = 1 - a := by
    linear_combination (norm := ring_nf) hcW + ((1 - a) * ((l + m) + 1)) * hu1
  have hsum2 : (l + m) * (1 - a) = 1 - 2 * a := by
    linear_combination (norm := ring_nf) hu1
  exact ⟨hc, by linear_combination (norm := ring_nf) hsum - hc - hsum2 + 2 * hu1⟩

private lemma zs4h_alg_main {a b c d pp r l m : ZMod p} (hlm : l * m = 1) (hne0 : l - m ≠ 0)
    (hl1 : l ≠ 1) (hl4 : l ^ 4 ≠ 1) (hl6 : l ^ 6 ≠ 1)
    (F1 : r * (l * b + m * a + c + d) = m * r) (F2 : r * (l * a + m * b + c + d) = l * r)
    (F3 : r * ((l + m) * pp) + c * c + d * d = c) (F4 : r * ((l + m) * pp) + 2 * c * d = d)
    (F5 : l ^ 2 * b * b + a * a + 2 * l * pp * r = m * b)
    (E1 : a * a + b * b + 2 * pp * r = 1) (E2 : a * b + pp * r = 0)
    (E3 : c * c + d * d + 2 * pp * r = 1) (E4 : c * d + pp * r = 0) :
    b = a - 1 ∧ c = 1 - a ∧ d = -a ∧ (l + m) - 2 ≠ 0 ∧ a * ((l + m) - 2) = (l + m) - 1 := by
  rcases eq_or_ne r 0 with hr | hr
  · exact (zs4h_alg_r0 hr hlm hl6 F5 E1 E2).elim
  obtain ⟨hb, hpr, hcd, hsum⟩ := zs4h_alg_r1 hr hne0 F1 F2 E2 E4
  have hu1 := zs4h_alg_hu (zs4h_alg_L hlm hl4) hb F3 F4 E2 E3 hpr hcd hsum
  obtain ⟨hc, hd⟩ := zs4h_alg_cd F3 hpr hcd hsum hu1
  exact ⟨hb, hc, hd, zs4h_alg_s2 hlm hl1,
    by linear_combination (norm := ring_nf) (-1 : ZMod p) * hu1⟩

private lemma zs4h_dvd_of_pow_eq_one {lam : (ZMod p)ˣ} (hlam : orderOf lam = 5) {k : ℕ}
    (hk : (lam : ZMod p) ^ k = 1) : 5 ∣ k := by
  rw [← hlam]
  exact orderOf_dvd_iff_pow_eq_one.mpr (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk))

private lemma zs4h_lam_ne {lam : (ZMod p)ˣ} (hlam : orderOf lam = 5) :
    (lam : ZMod p) ≠ 1 ∧ (lam : ZMod p) ^ 2 ≠ 1 ∧ (lam : ZMod p) ^ 4 ≠ 1 ∧
      (lam : ZMod p) ^ 6 ≠ 1 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := zs4h_dvd_of_pow_eq_one hlam (k := 1) (by rwa [pow_one])
    omega
  · have := zs4h_dvd_of_pow_eq_one hlam (k := 2) h
    omega
  · have := zs4h_dvd_of_pow_eq_one hlam (k := 4) h
    omega
  · have := zs4h_dvd_of_pow_eq_one hlam (k := 6) h
    omega

private lemma zs4h_two_ne_zero_of_order {lam : (ZMod p)ˣ} (hlam : orderOf lam = 5) :
    (2 : ZMod p) ≠ 0 := by
  intro hh
  have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hh
  rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h1 | h1
  · exact (Fact.out : p.Prime).ne_one h1
  · subst h1
    have h1' : lam = 1 := Subsingleton.elim lam 1
    rw [h1', orderOf_one] at hlam
    omega

private lemma zs4h_alg_ne0 {l : ZMod p} (hl0 : l ≠ 0) (hl2 : l ^ 2 ≠ 1) : l - l⁻¹ ≠ 0 := by
  intro hh
  have h1 : l = l⁻¹ := sub_eq_zero.mp hh
  apply hl2
  field_simp [hl0] at h1
  linear_combination h1

private lemma zs4h_shape_ex (f : Module.Basis (Fin 4) (ZMod p) U) {a₁ z a₄ : U ≃ₗ[ZMod p] U}
    (ha₁ : LinearMap.toMatrix f f a₁.toLinearMap = pijMat 0 1 1)
    (hz : LinearMap.toMatrix f f z.toLinearMap = -pijMat 2 3 1)
    (h₁ : a₁ * a₄ = a₄ * a₁) (hz₄ : z * a₄ = a₄ * z) :
    ∃ a b pp r c d : ZMod p, LinearMap.toMatrix f f a₄.toLinearMap =
      !![a, b, pp, pp; b, a, pp, pp; r, r, c, d; r, r, d, c] :=
  ⟨_, _, _, _, _, _, zs4h_shape f ha₁ hz h₁ hz₄⟩

private lemma zs4h_refl_mat (f : Module.Basis (Fin 4) (ZMod p) U) {lam : (ZMod p)ˣ}
    {a₂ a₄ : U ≃ₗ[ZMod p] U}
    (ha₂ : LinearMap.toMatrix f f a₂.toLinearMap = pijMat 0 1 (lam : ZMod p))
    (ha₄ : IsRefl p a₄) (h₂ : orderOf (a₂ * a₄) = 3) :
    LinearMap.toMatrix f f a₄.toLinearMap * LinearMap.toMatrix f f a₄.toLinearMap = 1 ∧
      (pijMat (0 : Fin 4) (1 : Fin 4) (lam : ZMod p) * LinearMap.toMatrix f f a₄.toLinearMap) ^ 2 =
        LinearMap.toMatrix f f a₄.toLinearMap * pijMat (0 : Fin 4) (1 : Fin 4) (lam : ZMod p) := by
  set M := LinearMap.toMatrix f f a₄.toLinearMap
  set P := pijMat (0 : Fin 4) (1 : Fin 4) (lam : ZMod p)
  have hmul : M * M = 1 := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap) ha₄.1
    simpa [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, LinearMap.toMatrix_one] using h
  have ha₂2 : a₂ * a₂ = 1 :=
    (isRefl_of_toMatrix_eq_pijMat f (by decide) (Units.ne_zero lam) ha₂).1
  have hpij : P * P = 1 := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap) ha₂2
    simpa [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, LinearMap.toMatrix_one, ha₂]
      using h
  have hcube : (P * M) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (a₂ * a₄)
    rw [h₂] at h
    have hprod : (a₂ * a₄) * (a₂ * a₄) * (a₂ * a₄) = 1 := by
      rwa [show (a₂ * a₄) * (a₂ * a₄) * (a₂ * a₄) = (a₂ * a₄) ^ 3 by
        rw [pow_succ, pow_succ, pow_one]]
    have h' : LinearMap.toMatrix f f ((a₂ * a₄) * (a₂ * a₄) * (a₂ * a₄)).toLinearMap = 1 := by
      rw [hprod]; exact LinearMap.toMatrix_one f
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, ha₂] at h'
    rw [show (P * M) ^ 3 = (P * M) * (P * M) * (P * M) from by rw [pow_succ, pow_succ, pow_one]]
    exact h'
  have hNa₂ : (P * M) * (M * P) = 1 := by
    rw [mul_assoc, ← mul_assoc M M P, hmul, one_mul, hpij]
  have h1 : (P * M) ^ 2 * (P * M) = 1 := by
    rw [← pow_succ]; exact hcube
  refine ⟨hmul, ?_⟩
  calc (P * M) ^ 2 = (P * M) ^ 2 * 1 := (mul_one _).symm
    _ = (P * M) ^ 2 * ((P * M) * (M * P)) := by rw [hNa₂]
    _ = ((P * M) ^ 2 * (P * M)) * (M * P) := by rw [← mul_assoc]
    _ = 1 * (M * P) := by rw [h1]
    _ = M * P := one_mul _

theorem toMatrix_refl_of_commute_pij (f : Module.Basis (Fin 4) (ZMod p) U) {lam : (ZMod p)ˣ}
    (hlam : orderOf lam = 5) {a₁ a₂ z a₄ : U ≃ₗ[ZMod p] U}
    (ha₁ : LinearMap.toMatrix f f a₁.toLinearMap = pijMat 0 1 1)
    (ha₂ : LinearMap.toMatrix f f a₂.toLinearMap = pijMat 0 1 (lam : ZMod p))
    (hz : LinearMap.toMatrix f f z.toLinearMap = -pijMat 2 3 1) (ha₄ : IsRefl p a₄)
    (h₁ : a₁ * a₄ = a₄ * a₁) (hz₄ : z * a₄ = a₄ * z) (h₂ : orderOf (a₂ * a₄) = 3) :
    ∃ u w : ZMod p, LinearMap.toMatrix f f a₄.toLinearMap =
      let s : ZMod p := (lam : ZMod p) + (lam⁻¹ : (ZMod p)ˣ)
      let x := (s - 1) / (s - 2)
      !![x, x - 1, w, w; x - 1, x, w, w; u, u, 1 - x, -x; u, u, -x, 1 - x] := by
  obtain ⟨a, b, pp, r, c, d, hshape⟩ := zs4h_shape_ex f ha₁ hz h₁ hz₄
  obtain ⟨hmul, hN2⟩ := zs4h_refl_mat f ha₂ ha₄ h₂
  rw [hshape] at hmul hN2
  have hl0 : (lam : ZMod p) ≠ 0 := Units.ne_zero lam
  obtain ⟨hl1, hl2, hl4, hl6⟩ := zs4h_lam_ne hlam
  obtain ⟨F1, F2, F3, F4, F5⟩ := zs4h_F_facts hl0 hN2
  obtain ⟨E1, E2, E3, E4⟩ := zs4h_E_facts (zs4h_two_ne_zero_of_order hlam) hmul
  obtain ⟨hb, hc, hd, hs2, ha⟩ := zs4h_alg_main (mul_inv_cancel₀ hl0) (zs4h_alg_ne0 hl0 hl2)
    hl1 hl4 hl6 F1 F2 F3 F4 F5 E1 E2 E3 E4
  have ha' := (eq_div_iff hs2).mpr ha
  refine ⟨r, pp, ?_⟩
  dsimp only
  rw [hshape, Units.val_inv_eq_inv_val, hb, hc, hd, ha']

private lemma zs4h_p_facts {lam : (ZMod p)ˣ} (hlam : orderOf lam = 5) :
    (3 : ZMod p) ≠ 0 ∧ (5 : ZMod p) ≠ 0 ∧ (37 : ZMod p) ≠ 0 := by
  have h5 : 5 ∣ p - 1 := by
    have h := orderOf_dvd_card (x := lam)
    rwa [hlam, ZMod.card_units p] at h
  have key : ∀ n : ℕ, n.Prime → ¬ 5 ∣ n - 1 → (n : ZMod p) ≠ 0 := by
    intro n hn hn5 hz
    have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hz
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hn).mp hdvd
    subst this
    exact hn5 h5
  refine ⟨?_, ?_, ?_⟩
  · simpa using key 3 Nat.prime_three (by omega)
  · simpa using key 5 Nat.prime_five (by omega)
  · simpa using key 37 (by norm_num) (by omega)

private lemma zs4h_two_ne_zero (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h'
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp h1

private lemma zs4h_pow_cayley {G : Matrix (Fin 4) (Fin 4) (ZMod p)} {v : Fin 4 → ZMod p}
    {t : ZMod p} (h : G.mulVec (G.mulVec v) = t • G.mulVec v - v) :
    (G ^ 2).mulVec v = t • G.mulVec v - (1 : ZMod p) • v ∧
    (G ^ 3).mulVec v = (t ^ 2 - 1) • G.mulVec v - t • v ∧
    (G ^ 4).mulVec v = (t ^ 3 - 2 * t) • G.mulVec v - (t ^ 2 - 1) • v ∧
    (G ^ 5).mulVec v = (t ^ 4 - 3 * t ^ 2 + 1) • G.mulVec v - (t ^ 3 - 2 * t) • v := by
  have e : ∀ k : ℕ, (G ^ (k + 1)).mulVec v = G.mulVec ((G ^ k).mulVec v) := fun k => by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
  have h2 : (G ^ 2).mulVec v = t • G.mulVec v - (1 : ZMod p) • v := by
    rw [e 1, pow_one, h, one_smul]
  have h3 : (G ^ 3).mulVec v = (t ^ 2 - 1) • G.mulVec v - t • v := by
    rw [e 2, h2, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, h]; module
  have h4 : (G ^ 4).mulVec v = (t ^ 3 - 2 * t) • G.mulVec v - (t ^ 2 - 1) • v := by
    rw [e 3, h3, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, h]; module
  have h5 : (G ^ 5).mulVec v = (t ^ 4 - 3 * t ^ 2 + 1) • G.mulVec v - (t ^ 3 - 2 * t) • v := by
    rw [e 4, h4, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, h]; module
  exact ⟨h2, h3, h4, h5⟩

private lemma zs4h_ord_act {S R : Matrix (Fin 4) (Fin 4) (ZMod p)} {r r' : Fin 4 → ZMod p}
    {u w : ZMod p} (hS1 : S.mulVec r = -r) (hS2 : S.mulVec r' = r' - u • r)
    (hR1 : R.mulVec r = r - w • r') (hR2 : R.mulVec r' = -r') :
    (S * R).mulVec r = (u * w - 1) • r - w • r' ∧ (S * R).mulVec r' = u • r - r' ∧
    (S * R).mulVec ((S * R).mulVec r) = (u * w - 2) • (S * R).mulVec r - r ∧
    (S * R).mulVec ((S * R).mulVec r') = (u * w - 2) • (S * R).mulVec r' - r' := by
  have hG1 : (S * R).mulVec r = (u * w - 1) • r - w • r' := by
    rw [← Matrix.mulVec_mulVec, hR1, Matrix.mulVec_sub, Matrix.mulVec_smul, hS1, hS2]
    module
  have hG2 : (S * R).mulVec r' = u • r - r' := by
    rw [← Matrix.mulVec_mulVec, hR2, Matrix.mulVec_neg, hS2]; module
  refine ⟨hG1, hG2, ?_, ?_⟩
  · rw [hG1]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hG1, hG2]
    module
  · rw [hG2]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hG1, hG2]
    module

private lemma zs4h_ord_main {G : Matrix (Fin 4) (Fin 4) (ZMod p)} {r r' : Fin 4 → ZMod p}
    {u w : ZMod p} (hG1 : G.mulVec r = (u * w - 1) • r - w • r')
    (hG2 : G.mulVec r' = u • r - r')
    (hind : ∀ α β : ZMod p, α • r + β • r' = 0 → α = 0 ∧ β = 0) {m : ℕ} (hGm : G ^ m = 1)
    {A B : ZMod p} (hr : (G ^ m).mulVec r = A • G.mulVec r - B • r)
    (hr' : (G ^ m).mulVec r' = A • G.mulVec r' - B • r') :
    A * (u * w - 1) - B - 1 = 0 ∧ A * w = 0 ∧ A * u = 0 ∧ A + B + 1 = 0 := by
  rw [hGm, Matrix.one_mulVec, hG1] at hr
  rw [hGm, Matrix.one_mulVec, hG2] at hr'
  have h1 : (A * (u * w - 1) - B - 1) • r + (-(A * w)) • r' = 0 := by
    have e : (A * (u * w - 1) - B - 1) • r + (-(A * w)) • r' =
        (A • ((u * w - 1) • r - w • r') - B • r) - r := by module
    rw [e, ← hr, sub_self]
  have h2 : (A * u) • r + (-(A + B + 1)) • r' = 0 := by
    have e : (A * u) • r + (-(A + B + 1)) • r' = (A • (u • r - r') - B • r') - r' := by
      module
    rw [e, ← hr', sub_self]
  obtain ⟨k1, k2⟩ := hind _ _ h1
  obtain ⟨k3, k4⟩ := hind _ _ h2
  exact ⟨k1, by linear_combination -k2, k3, by linear_combination -k4⟩

private lemma zs4h_ord_hA {u w : ZMod p} (hne : ¬ (u = 0 ∧ w = 0)) :
    ∀ A : ZMod p, A * u = 0 → A * w = 0 → A = 0 := by
  intro A h3 h4
  by_contra hA
  exact hne ⟨(mul_eq_zero.mp h3).resolve_left hA, (mul_eq_zero.mp h4).resolve_left hA⟩

private theorem zs4h_ord (hp : p ≠ 2) {S R : Matrix (Fin 4) (Fin 4) (ZMod p)}
    {r r' : Fin 4 → ZMod p} {u w : ZMod p}
    (hS1 : S.mulVec r = -r) (hS2 : S.mulVec r' = r' - u • r)
    (hR1 : R.mulVec r = r - w • r') (hR2 : R.mulVec r' = -r')
    (hind : ∀ α β : ZMod p, α • r + β • r' = 0 → α = 0 ∧ β = 0)
    {m : ℕ} (hm1 : 1 ≤ m) (hm5 : m ≤ 5) (hG : (S * R) ^ m = 1) :
    (u = 0 ∧ w = 0) ∨ (u * w - 1) * (u * w - 2) * ((u * w) ^ 2 - 3 * (u * w) + 1) = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := zs4h_two_ne_zero hp
  obtain ⟨hG1, hG2, hC1, hC2⟩ := zs4h_ord_act hS1 hS2 hR1 hR2
  obtain ⟨c2, c3, c4, c5⟩ := zs4h_pow_cayley hC1
  obtain ⟨d2, d3, d4, d5⟩ := zs4h_pow_cayley hC2
  by_cases hne : u = 0 ∧ w = 0
  · exact Or.inl hne
  right
  have hA := zs4h_ord_hA hne
  interval_cases m
  · obtain ⟨-, -, -, k4⟩ := zs4h_ord_main hG1 hG2 hind hG (A := 1) (B := 0) (by simp) (by simp)
    exact absurd (by linear_combination k4) h2
  · obtain ⟨-, k2, k3, k4⟩ := zs4h_ord_main hG1 hG2 hind hG c2 d2
    have h0 := hA _ k3 k2
    exact absurd (by linear_combination k4 - h0) h2
  · obtain ⟨-, k2, k3, k4⟩ := zs4h_ord_main hG1 hG2 hind hG c3 d3
    have h0 := hA _ k3 k2
    have hf : u * w - 1 = 0 := by linear_combination k4 - h0
    linear_combination ((u * w - 2) * ((u * w) ^ 2 - 3 * (u * w) + 1)) * hf
  · obtain ⟨-, k2, k3, k4⟩ := zs4h_ord_main hG1 hG2 hind hG c4 d4
    have h0 := hA _ k3 k2
    have h1 : (u * w - 2) ^ 2 = 0 := by linear_combination k4 - h0
    have hf : u * w - 2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    linear_combination ((u * w - 1) * ((u * w) ^ 2 - 3 * (u * w) + 1)) * hf
  · obtain ⟨-, k2, k3, k4⟩ := zs4h_ord_main hG1 hG2 hind hG c5 d5
    have h0 := hA _ k3 k2
    have hf : (u * w) ^ 2 - 3 * (u * w) + 1 = 0 := by
      linear_combination (u * w - 2) * (k4 - h0) - h0
    linear_combination ((u * w - 1) * (u * w - 2)) * hf

private lemma zs4h_refl_mulVec (r φ v : Fin 4 → ZMod p) :
    (1 - Matrix.vecMulVec r φ).mulVec v = v - dotProduct φ v • r := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  simp

private lemma zs4h_conj_refl {Z P : Matrix (Fin 4) (Fin 4) (ZMod p)} (hZ : Z * Z = 1)
    {r φ : Fin 4 → ZMod p} (hP : P = 1 - Matrix.vecMulVec r φ) :
    Z * P * Z = 1 - Matrix.vecMulVec (Z.mulVec r) (Z.vecMul φ) := by
  rw [hP, mul_sub, sub_mul, mul_one, hZ, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private lemma zs4h_pij12_eq (η : ZMod p) (hη : η ≠ 0) :
    pijMat (1 : Fin 4) (2 : Fin 4) η =
      1 - Matrix.vecMulVec ![0, 1, -η⁻¹, 0] ![0, 1, -η, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pijMat, hη]

private lemma zs4h_pij02_eq (η : ZMod p) (hη : η ≠ 0) :
    pijMat (0 : Fin 4) (2 : Fin 4) η =
      1 - Matrix.vecMulVec ![1, 0, -η⁻¹, 0] ![1, 0, -η, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pijMat, hη]

private theorem zs4h_s_rel {l : ZMod p} (hl : l ≠ 0) (hΦ : l ^ 4 + l ^ 3 + l ^ 2 + l + 1 = 0) :
    (l + l⁻¹) * (l + l⁻¹) + (l + l⁻¹) - 1 = 0 := by
  have hinv : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  linear_combination (l⁻¹) ^ 2 * hΦ + (2 - (l * l⁻¹ + 1) * (l ^ 2 + l + 1) - l⁻¹) * hinv

private theorem zs4h_t2_rel {l : ZMod p} (hl : l ≠ 0)
    (hs : (l + l⁻¹) * (l + l⁻¹) + (l + l⁻¹) - 1 = 0) :
    l ^ 2 + (l ^ 2)⁻¹ = -1 - (l + l⁻¹) := by
  have hinv : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  rw [← inv_pow]
  linear_combination hs - 2 * hinv

private theorem zs4h_alg_cancel {a s t₀ t₁ t₂ : ZMod p} (hs : s * s + s - 1 = 0) (ha : a ≠ 0)
    (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0) (h5 : (5 : ZMod p) ≠ 0)
    (h37 : (37 : ZMod p) ≠ 0) (e₀ : t₀ = 2) (e₁ : t₁ = s) (e₂ : t₂ = -1 - s)
    (h : (a ^ 2 - 1) * (a ^ 2 - 2) * ((a ^ 2) ^ 2 - 3 * a ^ 2 + 1) = 0)
    (h₀ : (a ^ 2 - a * t₀ + 1 - 1) * (a ^ 2 - a * t₀ + 1 - 2) *
      ((a ^ 2 - a * t₀ + 1) ^ 2 - 3 * (a ^ 2 - a * t₀ + 1) + 1) = 0)
    (h₁ : (a ^ 2 - a * t₁ + 1 - 1) * (a ^ 2 - a * t₁ + 1 - 2) *
      ((a ^ 2 - a * t₁ + 1) ^ 2 - 3 * (a ^ 2 - a * t₁ + 1) + 1) = 0)
    (h₂ : (a ^ 2 - a * t₂ + 1 - 1) * (a ^ 2 - a * t₂ + 1 - 2) *
      ((a ^ 2 - a * t₂ + 1) ^ 2 - 3 * (a ^ 2 - a * t₂ + 1) + 1) = 0) : False := by
  rw [e₀] at h₀
  rw [e₁] at h₁
  rw [e₂] at h₂
  have hS : 5 * a ^ 2 * (a ^ 6 + 10 * a ^ 4 - 6 * a ^ 2 + 1) = 0 := by
    linear_combination h₀ + 2 * h₁ + 2 * h₂ -
      (4 * a ^ 4 * s ^ 2 + 4 * a ^ 4 * s + 24 * a ^ 6 + 24 * a ^ 5 - 12 * a ^ 4 - 12 * a ^ 3) * hs
  have hQ : a ^ 6 + 10 * a ^ 4 - 6 * a ^ 2 + 1 = 0 :=
    (mul_eq_zero.mp hS).resolve_left (mul_ne_zero h5 (pow_ne_zero 2 ha))
  have h3552 : (3552 : ZMod p) = 0 := by
    linear_combination (6608 * (a ^ 2) ^ 2 + 68344 * a ^ 2 - 16328) * h +
      (-6608 * (a ^ 2) ^ 3 + 37384 * (a ^ 2) ^ 2 - 66392 * a ^ 2 + 36208) * hQ
  have hne : (3552 : ZMod p) ≠ 0 := by
    have : (3552 : ZMod p) = 2 ^ 5 * 3 * 37 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 5 h2) h3) h37
  exact hne h3552

private theorem zs4h_alg_a1 {a s : ZMod p} (hs : s * s + s - 1 = 0) (h2 : (2 : ZMod p) ≠ 0)
    (ha : a = 1) (h : (a ^ 2 - a * s + 1 - 1) * (a ^ 2 - a * s + 1 - 2) *
      ((a ^ 2 - a * s + 1) ^ 2 - 3 * (a ^ 2 - a * s + 1) + 1) = 0) : False := by
  subst ha
  have h4 : 2 * s ^ 4 = 0 := by linear_combination h + (s ^ 2 + s) * hs
  have hs0 : s = 0 := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp
    ((mul_eq_zero.mp h4).resolve_left h2)
  rw [hs0] at hs
  norm_num at hs

private theorem zs4h_alg_sum {l u w : ZMod p} (hΦ : l ^ 4 + l ^ 3 + l ^ 2 + l + 1 = 0)
    {q₀ q₁ q₂ q₃ q₄ : ZMod p} (e₀ : q₀ = u + w) (e₁ : q₁ = l * u + l ^ 4 * w)
    (e₂ : q₂ = l ^ 2 * u + l ^ 3 * w) (e₃ : q₃ = l ^ 3 * u + l ^ 2 * w)
    (e₄ : q₄ = l ^ 4 * u + l * w)
    (h₀ : q₀ * (q₀ - 1) * (q₀ ^ 2 - q₀ - 1) = 0) (h₁ : q₁ * (q₁ - 1) * (q₁ ^ 2 - q₁ - 1) = 0)
    (h₂ : q₂ * (q₂ - 1) * (q₂ ^ 2 - q₂ - 1) = 0) (h₃ : q₃ * (q₃ - 1) * (q₃ ^ 2 - q₃ - 1) = 0)
    (h₄ : q₄ * (q₄ - 1) * (q₄ ^ 2 - q₄ - 1) = 0) : 30 * (u * w) ^ 2 = 0 := by
  subst e₀ e₁ e₂ e₃ e₄
  linear_combination h₀ + h₁ + h₂ + h₃ + h₄ - (
    l ^ 12 * u ^ 4 + l ^ 12 * w ^ 4 - l ^ 11 * u ^ 4 - l ^ 11 * w ^ 4 + 4 * l ^ 9 * u ^ 3 * w +
    4 * l ^ 9 * u * w ^ 3 + l ^ 8 * u ^ 4 - 4 * l ^ 8 * u ^ 3 * w - 4 * l ^ 8 * u * w ^ 3 +
    l ^ 8 * w ^ 4 - 2 * l ^ 8 * u ^ 3 + 4 * l ^ 7 * u ^ 3 * w - 2 * l ^ 8 * w ^ 3 +
    4 * l ^ 7 * u * w ^ 3 + 2 * l ^ 7 * u ^ 3 - l ^ 6 * u ^ 4 - 4 * l ^ 6 * u ^ 3 * w +
    24 * l ^ 6 * u ^ 2 * w ^ 2 + 2 * l ^ 7 * w ^ 3 - 4 * l ^ 6 * u * w ^ 3 - l ^ 6 * w ^ 4 +
    4 * l ^ 5 * u ^ 3 * w - 24 * l ^ 5 * u ^ 2 * w ^ 2 + 4 * l ^ 5 * u * w ^ 3 -
    2 * l ^ 5 * u ^ 3 + l ^ 4 * u ^ 4 - 6 * l ^ 5 * u ^ 2 * w - 6 * l ^ 5 * u * w ^ 2 -
    2 * l ^ 5 * w ^ 3 + l ^ 4 * w ^ 4 + 2 * l ^ 4 * u ^ 3 + 2 * l ^ 4 * w ^ 3 -
    2 * l ^ 3 * u ^ 3 - 2 * l ^ 3 * w ^ 3 - l * u ^ 4 - 4 * l * u ^ 3 * w +
    24 * l * u ^ 2 * w ^ 2 - 4 * l * u * w ^ 3 - l * w ^ 4 + 2 * l * u ^ 3 + u ^ 4 +
    6 * l * u ^ 2 * w + 4 * u ^ 3 * w + 6 * l * u * w ^ 2 - 24 * u ^ 2 * w ^ 2 +
    2 * l * w ^ 3 + 4 * u * w ^ 3 + w ^ 4 - 2 * u ^ 3 - 6 * u ^ 2 * w - 6 * u * w ^ 2 -
    2 * w ^ 3 + u + w) * hΦ

namespace FourThreeData

variable [Module.Finite (ZMod p) U] {f : Module.Basis (Fin 4) (ZMod p) U} {lam : (ZMod p)ˣ}
  {a₁ a₂ a₃ a₄ : U ≃ₗ[ZMod p] U} {K F : Subgroup (U ≃ₗ[ZMod p] U)}

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_orderOf_pij_mul (f : Module.Basis (Fin 4) (ZMod p) U) {lam : (ZMod p)ˣ}
    (hlam : orderOf lam = 5) {a₁ a₂ : U ≃ₗ[ZMod p] U}
    (ha₁ : LinearMap.toMatrix f f a₁.toLinearMap = pijMat 0 1 1)
    (ha₂ : LinearMap.toMatrix f f a₂.toLinearMap = pijMat 0 1 (lam : ZMod p)) :
    orderOf (a₁ * a₂) = 5 := by
  have hmat : LinearMap.toMatrix f f (a₁ * a₂).toLinearMap =
      Matrix.diagonal (fun k : Fin 4 => if k = 0 then (lam : ZMod p)⁻¹
        else if k = 1 then (lam : ZMod p) else 1) := by
    rw [show (a₁ * a₂).toLinearMap = a₁.toLinearMap * a₂.toLinearMap from
      LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, ha₁, ha₂,
      pijMat_mul_pijMat (by decide : (0 : Fin 4) ≠ 1) (1 : ZMod p) (lam : ZMod p)]
    congr 1
    funext k
    fin_cases k <;> simp only [if_true, if_false, one_mul, inv_one, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceEq]
  rw [← orderOf_toMatrix f (a₁ * a₂), hmat, ← hlam, orderOf_eq_orderOf_iff]
  intro k
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one, Matrix.diagonal_injective.eq_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Pi.pow_apply, if_true] at h0
    rw [inv_pow, inv_eq_one] at h0
    exact Units.ext h0
  · intro h
    have h' : (lam : ZMod p) ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
    funext i
    fin_cases i
    · show ((lam : ZMod p)⁻¹) ^ k = 1
      rw [inv_pow, inv_eq_one]; exact h'
    · show (lam : ZMod p) ^ k = 1
      exact h'
    · show (1 : ZMod p) ^ k = 1
      exact one_pow k
    · show (1 : ZMod p) ^ k = 1
      exact one_pow k

omit [Module.Finite (ZMod p) U] in
theorem exists_conj (_hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) :
    ∃ a₄' ∈ F, FourThreeData f lam a₁ a₂ a₃ a₄' K F ∧
      orderOf (a₁ * a₄') = 2 ∧ orderOf (a₂ * a₄') = 3 := by
  let V := HardMathSupport.Kantor79.commutatorSpace F
  let ρ := restrictHom F V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective ρ := restrictHom_injective_of_splitSupport h.splitSupport_F
  have hr1 : IsRefl p a₁ := isRefl_of_toMatrix_eq_pijMat f (by decide) one_ne_zero h.toMatrix_a₁
  have hr2 : IsRefl p a₂ :=
    isRefl_of_toMatrix_eq_pijMat f (by decide) (Units.ne_zero lam) h.toMatrix_a₂
  have h12 : orderOf (a₁ * a₂) = 5 :=
    zs4h_orderOf_pij_mul f h.orderOf_lam h.toMatrix_a₁ h.toMatrix_a₂
  have h12' : orderOf (ρ ⟨a₁, h.a₁_mem⟩ * ρ ⟨a₂, h.a₂_mem⟩) = 5 := by
    rw [← map_mul, orderOf_injective ρ hinj, ← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact h12
  obtain ⟨g, hgA, hg1, hg2⟩ := h.h3.2 (ρ ⟨a₁, h.a₁_mem⟩) ⟨⟨a₁, h.a₁_mem⟩, rfl⟩
    (ρ ⟨a₂, h.a₂_mem⟩) ⟨⟨a₂, h.a₂_mem⟩, rfl⟩ (ρ ⟨a₄, h.a₄_mem⟩) ⟨⟨a₄, h.a₄_mem⟩, rfl⟩
    (isRefl_restrictHom_of_isRefl h.splitSupport_F hr1)
    (isRefl_restrictHom_of_isRefl h.splitSupport_F hr2)
    (isRefl_restrictHom_of_isRefl h.splitSupport_F h.isRefl_a₄) h12'
  obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.mp hgA
  set a₄' : U ≃ₗ[ZMod p] U := (g₀ : U ≃ₗ[ZMod p] U) * a₄ * (g₀ : U ≃ₗ[ZMod p] U)⁻¹ with ha₄'def
  have ha₄'mem : a₄' ∈ F := F.mul_mem (F.mul_mem g₀.2 h.a₄_mem) (F.inv_mem g₀.2)
  have hconj : ρ ⟨a₄', ha₄'mem⟩ = g * ρ ⟨a₄, h.a₄_mem⟩ * g⁻¹ := by
    have h1 : (⟨a₄', ha₄'mem⟩ : F) = ⟨(g₀ : U ≃ₗ[ZMod p] U), g₀.2⟩ * ⟨a₄, h.a₄_mem⟩ *
        ⟨(g₀ : U ≃ₗ[ZMod p] U), g₀.2⟩⁻¹ := by
      ext v
      simp [ha₄'def]
    rw [h1, map_mul, map_mul, map_inv, hg₀]
  refine ⟨a₄', ha₄'mem, ?_, ?_, ?_⟩
  · refine ⟨h.orderOf_lam, h.toMatrix_a₁, h.toMatrix_a₂, h.toMatrix_a₃,
      IsRefl.conj h.isRefl_a₄ (g₀ : U ≃ₗ[ZMod p] U), h.eq_K, h.irred, h.transvectionFree, h.dmax,
      h.a₁_mem, h.a₂_mem, ha₄'mem, h.splitSupport_F, h.h3, h.splitOfIrred, h.noOrth, h.negOfPrim⟩
  · have h1 : (⟨a₁ * a₄', F.mul_mem h.a₁_mem ha₄'mem⟩ : F) = ⟨a₁, h.a₁_mem⟩ * ⟨a₄', ha₄'mem⟩ := by
      ext; rfl
    have hord : orderOf (ρ ⟨a₁ * a₄', F.mul_mem h.a₁_mem ha₄'mem⟩) = 2 := by
      rw [h1, map_mul, hconj, hg1]
    rw [orderOf_injective ρ hinj, ← Subgroup.orderOf_coe] at hord
    exact hord
  · have h1 : (⟨a₂ * a₄', F.mul_mem h.a₂_mem ha₄'mem⟩ : F) = ⟨a₂, h.a₂_mem⟩ * ⟨a₄', ha₄'mem⟩ := by
      ext; rfl
    have hord : orderOf (ρ ⟨a₂ * a₄', F.mul_mem h.a₂_mem ha₄'mem⟩) = 3 := by
      rw [h1, map_mul, hconj, hg2]
    rw [orderOf_injective ρ hinj, ← Subgroup.orderOf_coe] at hord
    exact hord

omit [Module.Finite (ZMod p) U] in
private theorem eq_of_restrictHom_commutatorSpace_eq {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport F 3) {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : restrictHom F (HardMathSupport.Kantor79.commutatorSpace F)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨x, hx⟩ =
      restrictHom F (HardMathSupport.Kantor79.commutatorSpace F)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨y, hy⟩) : x = y := by
  ext v
  have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
    rw [hs.1.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
  have hxa : x a = y a := by
    have := congrArg (fun (e : HardMathSupport.Kantor79.commutatorSpace F ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace F) => (e ⟨a, ha⟩ : U)) hxy
    simpa [restrictHom_apply] using this
  have hxb : x b = b := (mem_centralizerSpace.mp hb) x hx
  have hyb : y b = b := (mem_centralizerSpace.mp hb) y hy
  rw [← hab, map_add, map_add, hxa, hxb, hyb]

omit [Module.Finite (ZMod p) U] in
private theorem ne_one_of_restrictHom_eq_neg {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport F 3) (hp2 : p ≠ 2) {z₀ : F}
    (hz₀ : restrictHom F (HardMathSupport.Kantor79.commutatorSpace F)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) z₀ = LinearEquiv.neg (ZMod p)) :
    (z₀ : U ≃ₗ[ZMod p] U) ≠ 1 := by
  intro hz1
  have hz0one : z₀ = 1 := Subtype.ext hz1
  have hneg : (LinearEquiv.neg (ZMod p) : HardMathSupport.Kantor79.commutatorSpace F ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace F) = 1 := by
    rw [← hz₀, hz0one, map_one]
  have hne : HardMathSupport.Kantor79.commutatorSpace F ≠ ⊥ := by
    intro hbot
    have hfin := hs.2.1
    rw [hbot] at hfin
    simp at hfin
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxneg : (⟨x, hx⟩ : HardMathSupport.Kantor79.commutatorSpace F) =
      -(⟨x, hx⟩ : HardMathSupport.Kantor79.commutatorSpace F) := by
    have := congrArg (fun (e : HardMathSupport.Kantor79.commutatorSpace F ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace F) => e ⟨x, hx⟩) hneg
    exact this.symm
  have hx_eq : x = -x := by
    have := congrArg (fun w : HardMathSupport.Kantor79.commutatorSpace F => (w : U)) hxneg
    simpa [Submodule.coe_neg] using this
  have htwo : (2 : ZMod p) • x = 0 := by
    have := congrArg (fun y => y + x) hx_eq
    rw [neg_add_cancel] at this
    rw [two_smul]; exact this
  have h2zero : (2 : ZMod p) = 0 := (smul_eq_zero.mp htwo).resolve_right hx0
  have hp_dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2zero
  rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd with h1 | h1
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp2 h1

theorem exists_centre (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) :
    ∃ z ∈ F, z ≠ 1 ∧ (∀ x ∈ F, z * x = x * z) ∧
      (∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, z v = -v) ∧
      ∀ v ∈ centralizerSpace F, z v = v := by
  obtain ⟨z₀, hz₀⟩ := MonoidHom.mem_range.mp h.h3.1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : lam = 1 := Subsingleton.elim lam 1
    have hord := h.orderOf_lam
    rw [h1, orderOf_one] at hord
    omega
  refine ⟨(z₀ : U ≃ₗ[ZMod p] U), z₀.2, ?_, ?_, ?_, ?_⟩
  · exact ne_one_of_restrictHom_eq_neg h.splitSupport_F hp2 hz₀
  · intro x hx
    apply eq_of_restrictHom_commutatorSpace_eq h.splitSupport_F (F.mul_mem z₀.2 hx)
      (F.mul_mem hx z₀.2)
    have h1 : (⟨z₀ * x, F.mul_mem z₀.2 hx⟩ : F) = ⟨z₀, z₀.2⟩ * ⟨x, hx⟩ := Subtype.ext rfl
    have h2 : (⟨x * z₀, F.mul_mem hx z₀.2⟩ : F) = ⟨x, hx⟩ * ⟨z₀, z₀.2⟩ := Subtype.ext rfl
    rw [h1, h2, map_mul, map_mul, hz₀]
    ext v; simp
  · intro v hv
    have := congrArg (fun (e : HardMathSupport.Kantor79.commutatorSpace F ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace F) => (e ⟨v, hv⟩ : U)) hz₀
    simpa [restrictHom_apply] using this
  · intro v hv
    exact (mem_centralizerSpace.mp hv) (z₀ : U ≃ₗ[ZMod p] U) z₀.2

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_toMatrix_mul (f : Module.Basis (Fin 4) (ZMod p) U)
    (x y : U ≃ₗ[ZMod p] U) :
    LinearMap.toMatrix f f ((x * y : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f x * LinearMap.toMatrix f f y := by
  rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_p_ne_two (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) : p ≠ 2 := by
  rintro rfl
  have h1 : lam = 1 := Subsingleton.elim lam 1
  have hord := h.orderOf_lam
  rw [h1, orderOf_one] at hord
  omega

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_gens_mem (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) :
    a₁ ∈ K ∧ a₂ ∈ K ∧ a₃ ∈ K := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [h.eq_K]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_refl_gens (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) :
    IsRefl p a₁ ∧ IsRefl p a₂ ∧ IsRefl p a₃ :=
  ⟨isRefl_of_toMatrix_eq_pijMat f (by decide) one_ne_zero h.toMatrix_a₁,
    isRefl_of_toMatrix_eq_pijMat f (by decide) (Units.ne_zero lam) h.toMatrix_a₂,
    isRefl_of_toMatrix_eq_pijMat f (by decide) one_ne_zero h.toMatrix_a₃⟩

private lemma zs4h_cb_alg {x y m : ZMod p} (hm : m ≠ 1) (h1 : x = y) (h2 : x = m * y) :
    x = 0 ∧ y = 0 := by
  have h3 : (1 - m) * y = 0 := by linear_combination h2 - h1
  have hy : y = 0 := (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hm.symm)
  exact ⟨by rw [h1, hy], hy⟩

private lemma zs4h_cb_top {Z : Matrix (Fin 4) (Fin 4) (ZMod p)} {l : ZMod p} (hl : l ≠ l⁻¹)
    (hc1 : pijMat (0 : Fin 4) (1 : Fin 4) 1 * Z = Z * pijMat (0 : Fin 4) (1 : Fin 4) 1)
    (hc2 : pijMat (0 : Fin 4) (1 : Fin 4) l * Z = Z * pijMat (0 : Fin 4) (1 : Fin 4) l) :
    Z 0 0 = Z 1 1 ∧ Z 0 1 = 0 ∧ Z 1 0 = 0 := by
  have e00 : Z 0 0 = Z 1 1 := by
    have hh := congrFun (congrFun hc1 1) 0
    rw [(zs4h_pij01_mul_apply 1 Z 0).2.1, (zs4h_mul_pij01_apply 1 Z 1).1] at hh
    simpa using hh
  have e10 : Z 1 0 = Z 0 1 := by
    have hh := congrFun (congrFun hc1 0) 0
    rw [(zs4h_pij01_mul_apply 1 Z 0).1, (zs4h_mul_pij01_apply 1 Z 0).1] at hh
    simpa using hh
  have e01 : Z 0 1 = 0 := by
    have hl' : l * Z 1 0 = l⁻¹ * Z 0 1 := by
      have hh := congrFun (congrFun hc2 0) 0
      rw [(zs4h_pij01_mul_apply l Z 0).1, (zs4h_mul_pij01_apply l Z 0).1] at hh
      exact hh
    rw [e10] at hl'
    have h2 : (l - l⁻¹) * Z 0 1 = 0 := by linear_combination hl'
    rcases mul_eq_zero.mp h2 with hh | hh
    · exact absurd (sub_eq_zero.mp hh) hl
    · exact hh
  exact ⟨e00, e01, by rw [e10, e01]⟩

private lemma zs4h_cb_up {Z : Matrix (Fin 4) (Fin 4) (ZMod p)} {l : ZMod p} (hl : l ≠ 1)
    (hc1 : pijMat (0 : Fin 4) (1 : Fin 4) 1 * Z = Z * pijMat (0 : Fin 4) (1 : Fin 4) 1)
    (hc2 : pijMat (0 : Fin 4) (1 : Fin 4) l * Z = Z * pijMat (0 : Fin 4) (1 : Fin 4) l) :
    Z 0 2 = 0 ∧ Z 1 2 = 0 ∧ Z 0 3 = 0 ∧ Z 1 3 = 0 := by
  have a1 : Z 0 2 = Z 1 2 := by
    have hh := congrFun (congrFun hc1 1) 2
    rw [(zs4h_pij01_mul_apply 1 Z 2).2.1, (zs4h_mul_pij01_apply 1 Z 1).2.2.1] at hh
    simpa using hh
  have a2 : l * Z 1 2 = Z 0 2 := by
    have hh := congrFun (congrFun hc2 0) 2
    rw [(zs4h_pij01_mul_apply l Z 2).1, (zs4h_mul_pij01_apply l Z 0).2.2.1] at hh
    simpa using hh
  have b1 : Z 0 3 = Z 1 3 := by
    have hh := congrFun (congrFun hc1 1) 3
    rw [(zs4h_pij01_mul_apply 1 Z 3).2.1, (zs4h_mul_pij01_apply 1 Z 1).2.2.2] at hh
    simpa using hh
  have b2 : l * Z 1 3 = Z 0 3 := by
    have hh := congrFun (congrFun hc2 0) 3
    rw [(zs4h_pij01_mul_apply l Z 3).1, (zs4h_mul_pij01_apply l Z 0).2.2.2] at hh
    simpa using hh
  obtain ⟨x2, y2⟩ := zs4h_cb_alg hl a1 a2.symm
  obtain ⟨x3, y3⟩ := zs4h_cb_alg hl b1 b2.symm
  exact ⟨x2, y2, x3, y3⟩

private lemma zs4h_cb_down {Z : Matrix (Fin 4) (Fin 4) (ZMod p)} {l : ZMod p} (hl : l⁻¹ ≠ 1)
    (hc1 : pijMat (0 : Fin 4) (1 : Fin 4) 1 * Z = Z * pijMat (0 : Fin 4) (1 : Fin 4) 1)
    (hc2 : pijMat (0 : Fin 4) (1 : Fin 4) l * Z = Z * pijMat (0 : Fin 4) (1 : Fin 4) l) :
    Z 2 0 = 0 ∧ Z 2 1 = 0 ∧ Z 3 0 = 0 ∧ Z 3 1 = 0 := by
  have a1 : Z 2 0 = Z 2 1 := by
    have hh := congrFun (congrFun hc1 2) 0
    rw [(zs4h_pij01_mul_apply 1 Z 0).2.2.1, (zs4h_mul_pij01_apply 1 Z 2).1] at hh
    simpa only [inv_one, one_mul] using hh
  have a2 : Z 2 0 = l⁻¹ * Z 2 1 := by
    have hh := congrFun (congrFun hc2 2) 0
    rw [(zs4h_pij01_mul_apply l Z 0).2.2.1, (zs4h_mul_pij01_apply l Z 2).1] at hh
    exact hh
  have b1 : Z 3 0 = Z 3 1 := by
    have hh := congrFun (congrFun hc1 3) 0
    rw [(zs4h_pij01_mul_apply 1 Z 0).2.2.2, (zs4h_mul_pij01_apply 1 Z 3).1] at hh
    simpa only [inv_one, one_mul] using hh
  have b2 : Z 3 0 = l⁻¹ * Z 3 1 := by
    have hh := congrFun (congrFun hc2 3) 0
    rw [(zs4h_pij01_mul_apply l Z 0).2.2.2, (zs4h_mul_pij01_apply l Z 3).1] at hh
    exact hh
  obtain ⟨x2, y2⟩ := zs4h_cb_alg hl a1 a2
  obtain ⟨x3, y3⟩ := zs4h_cb_alg hl b1 b2
  exact ⟨x2, y2, x3, y3⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_comm_mat (f : Module.Basis (Fin 4) (ZMod p) U) {z a : U ≃ₗ[ZMod p] U}
    {A : Matrix (Fin 4) (Fin 4) (ZMod p)} (ha : LinearMap.toMatrix f f a.toLinearMap = A)
    (hc : z * a = a * z) :
    A * LinearMap.toMatrix f f z.toLinearMap = LinearMap.toMatrix f f z.toLinearMap * A := by
  have hh := congrArg (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap) hc
  rw [zs4h_toMatrix_mul, zs4h_toMatrix_mul, ha] at hh
  exact hh.symm

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_cb_hz00 (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) {z : U ≃ₗ[ZMod p] U}
    (hz : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, z v = -v)
    (e01 : LinearMap.toMatrix f f z.toLinearMap 0 1 = 0) :
    LinearMap.toMatrix f f z.toLinearMap 0 0 = -1 := by
  set Z := LinearMap.toMatrix f f z.toLinearMap with hZdef
  have hZ : ∀ k j : Fin 4, Z k j = f.repr (z (f j)) k := fun k j =>
    LinearMap.toMatrix_apply f f z.toLinearMap k j
  have ha₁f : (a₁ : U ≃ₗ[ZMod p] U) (f 0) = f 1 := by
    apply f.repr.injective
    ext k
    rw [show f.repr ((a₁ : U ≃ₗ[ZMod p] U) (f 0)) k =
        LinearMap.toMatrix f f (a₁ : U →ₗ[ZMod p] U) k 0 from
      (LinearMap.toMatrix_apply f f (a₁ : U →ₗ[ZMod p] U) k 0).symm]
    rw [h.toMatrix_a₁]
    fin_cases k <;> simp [pijMat, Module.Basis.repr_self]
  have hmoved : f 0 - f 1 ∈ HardMathSupport.Kantor79.commutatorSpace F := by
    have h1 : f 0 - f 1 = -((a₁ : U ≃ₗ[ZMod p] U) (f 0) - f 0) := by rw [ha₁f]; abel
    rw [h1]
    exact neg_mem (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace h.a₁_mem ⟨f 0, rfl⟩)
  have h1 := congrArg (fun v => f.repr v 0) (hz _ hmoved)
  have h2 : f.repr (z (f 0 - f 1)) 0 = Z 0 0 - Z 0 1 := by
    simp only [map_sub, Finsupp.sub_apply, ← hZ 0 0, ← hZ 0 1]
  have h3 : f.repr (-(f 0 - f 1)) 0 = -1 := by
    simp [Module.Basis.repr_self]
  rw [h2, h3] at h1
  rw [e01, sub_zero] at h1
  exact h1

omit [Module.Finite (ZMod p) U] in
theorem toMatrix_centre_block (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) {z : U ≃ₗ[ZMod p] U}
    (_hzF : z ∈ F) (hzc : ∀ x ∈ F, z * x = x * z)
    (hz : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, z v = -v)
    (_hz' : ∀ v ∈ centralizerSpace F, z v = v) (i j : Fin 4) (hij : i.val < 2 ∨ j.val < 2) :
    LinearMap.toMatrix f f z.toLinearMap i j = if i = j then -1 else 0 := by
  have hc1 := zs4h_comm_mat f h.toMatrix_a₁ (hzc a₁ h.a₁_mem)
  have hc2 := zs4h_comm_mat f h.toMatrix_a₂ (hzc a₂ h.a₂_mem)
  obtain ⟨hl1, hl2, -⟩ := zs4h_lam_ne h.orderOf_lam
  obtain ⟨e00, e01, e10⟩ :=
    zs4h_cb_top (sub_ne_zero.mp (zs4h_alg_ne0 (Units.ne_zero lam) hl2)) hc1 hc2
  obtain ⟨o02, o12, o03, o13⟩ := zs4h_cb_up hl1 hc1 hc2
  obtain ⟨o20, o21, o30, o31⟩ := zs4h_cb_down (fun hh => hl1 (inv_eq_one.mp hh)) hc1 hc2
  have hz00 := zs4h_cb_hz00 h hz e01
  have e11 : LinearMap.toMatrix f f z.toLinearMap 1 1 = -1 := by rw [← e00, hz00]
  rcases hij with hi | hj
  · fin_cases i <;> fin_cases j <;>
      simp only [Fin.reduceFinMk, Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true]
    all_goals first
      | exact hz00 | exact e01 | exact e10 | exact e11
      | exact o02 | exact o12 | exact o03 | exact o13
      | (exfalso; simp at hi)
  · fin_cases j <;> fin_cases i <;>
      simp only [Fin.reduceFinMk, Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true]
    all_goals first
      | exact hz00 | exact e01 | exact e10 | exact e11
      | exact o20 | exact o21 | exact o30 | exact o31
      | (exfalso; simp at hj)

private lemma zs4h_finite_equiv : Finite (U ≃ₗ[ZMod p] U) := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective

private theorem zs4h_pair (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ K) (hy : y ∈ K) (hxr : IsRefl p x) (hyr : IsRefl p y)
    {r r' φ φ' : Fin 4 → ZMod p}
    (hS : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec r φ)
    (hR : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec r' φ')
    (hφ : dotProduct φ r = 2) (hφ' : dotProduct φ' r' = 2)
    (hind : ∀ α β : ZMod p, α • r + β • r' = 0 → α = 0 ∧ β = 0) :
    (dotProduct φ r' = 0 ∧ dotProduct φ' r = 0) ∨
      (dotProduct φ r' * dotProduct φ' r - 1) * (dotProduct φ r' * dotProduct φ' r - 2) *
        ((dotProduct φ r' * dotProduct φ' r) ^ 2 - 3 * (dotProduct φ r' * dotProduct φ' r) + 1)
        = 0 := by
  have hfin : Finite (U ≃ₗ[ZMod p] U) := zs4h_finite_equiv
  have hle := h.dmax.1 x hx y hy hxr hyr
  have hpos : 0 < orderOf (x * y) := orderOf_pos _
  obtain ⟨m, hm⟩ : ∃ m, m = orderOf (x * y) := ⟨_, rfl⟩
  rw [← hm] at hle hpos
  have hG : (LinearMap.toMatrix f f x.toLinearMap * LinearMap.toMatrix f f y.toLinearMap) ^
      m = 1 := by
    rw [hm, ← zs4h_toMatrix_mul, ← orderOf_toMatrix f (x * y)]
    exact pow_orderOf_eq_one _
  rw [hS, hR] at hG
  refine zs4h_ord hp ?_ ?_ ?_ ?_ hind hpos hle hG
  · rw [zs4h_refl_mulVec, hφ]; module
  · rw [zs4h_refl_mulVec]
  · rw [zs4h_refl_mulVec]
  · rw [zs4h_refl_mulVec, hφ']; module

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_toMatrix_a1a2 (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) :
    LinearMap.toMatrix f f (a₁ * a₂).toLinearMap = Matrix.diagonal (fun k : Fin 4 =>
      if k = 0 then (lam : ZMod p)⁻¹ else if k = 1 then (lam : ZMod p) else 1) := by
  rw [show (a₁ * a₂).toLinearMap = a₁.toLinearMap * a₂.toLinearMap from
    LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, h.toMatrix_a₁, h.toMatrix_a₂,
    pijMat_mul_pijMat (by decide : (0 : Fin 4) ≠ 1) (1 : ZMod p) (lam : ZMod p)]
  congr 1
  funext k
  fin_cases k <;> simp only [if_true, if_false, one_mul, inv_one, Fin.isValue,
    Fin.zero_eta, Fin.mk_one, Fin.reduceEq]

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_toMatrix_a2a1 (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) :
    LinearMap.toMatrix f f (a₂ * a₁).toLinearMap = Matrix.diagonal (fun k : Fin 4 =>
      if k = 0 then (lam : ZMod p) else if k = 1 then (lam : ZMod p)⁻¹ else 1) := by
  rw [show (a₂ * a₁).toLinearMap = a₂.toLinearMap * a₁.toLinearMap from
    LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, h.toMatrix_a₁, h.toMatrix_a₂,
    pijMat_mul_pijMat (by decide : (0 : Fin 4) ≠ 1) (lam : ZMod p) (1 : ZMod p)]
  congr 1
  funext k
  fin_cases k <;> simp only [if_true, if_false, mul_one, inv_one, Fin.isValue,
    Fin.zero_eta, Fin.mk_one, Fin.reduceEq]

private lemma zs4h_diag_pij12 {l α : ZMod p} (hl : l ≠ 0) :
    Matrix.diagonal (fun k : Fin 4 => if k = 0 then l⁻¹ else if k = 1 then l else 1) *
      pijMat (1 : Fin 4) (2 : Fin 4) α *
      Matrix.diagonal (fun k : Fin 4 => if k = 0 then l else if k = 1 then l⁻¹ else 1) =
      pijMat 1 2 (l * α) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal, pijMat, hl]

private lemma zs4h_diag_pij02 {l α : ZMod p} (hl : l ≠ 0) :
    Matrix.diagonal (fun k : Fin 4 => if k = 0 then l else if k = 1 then l⁻¹ else 1) *
      pijMat (0 : Fin 4) (2 : Fin 4) α *
      Matrix.diagonal (fun k : Fin 4 => if k = 0 then l⁻¹ else if k = 1 then l else 1) =
      pijMat 0 2 (l * α) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal, pijMat, hl]

private lemma zs4h_conj_pij01 :
    pijMat (1 : Fin 4) (2 : Fin 4) (1 : ZMod p) * pijMat (0 : Fin 4) (1 : Fin 4) 1 *
      pijMat (1 : Fin 4) (2 : Fin 4) 1 = pijMat 0 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat]

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_mem_pij12 (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) (k : ℕ) :
    ∃ x ∈ K, LinearMap.toMatrix f f x.toLinearMap = pijMat 1 2 ((lam : ZMod p) ^ k) := by
  induction k with
  | zero => exact ⟨a₃, (zs4h_gens_mem h).2.2, by simpa using h.toMatrix_a₃⟩
  | succ k ih =>
    obtain ⟨x, hxK, hx⟩ := ih
    obtain ⟨h1, h2, -⟩ := zs4h_gens_mem h
    refine ⟨(a₁ * a₂) * x * (a₂ * a₁),
      K.mul_mem (K.mul_mem (K.mul_mem h1 h2) hxK) (K.mul_mem h2 h1), ?_⟩
    rw [zs4h_toMatrix_mul, zs4h_toMatrix_mul, zs4h_toMatrix_a1a2 h, hx, zs4h_toMatrix_a2a1 h,
      zs4h_diag_pij12 (Units.ne_zero lam), pow_succ']

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_mem_pij02 (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) (k : ℕ) :
    ∃ x ∈ K, LinearMap.toMatrix f f x.toLinearMap = pijMat 0 2 ((lam : ZMod p) ^ k) := by
  induction k with
  | zero =>
    obtain ⟨h1, -, h3⟩ := zs4h_gens_mem h
    refine ⟨a₃ * a₁ * a₃, K.mul_mem (K.mul_mem h3 h1) h3, ?_⟩
    rw [zs4h_toMatrix_mul, zs4h_toMatrix_mul, h.toMatrix_a₁, h.toMatrix_a₃, zs4h_conj_pij01,
      pow_zero]
  | succ k ih =>
    obtain ⟨x, hxK, hx⟩ := ih
    obtain ⟨h1, h2, -⟩ := zs4h_gens_mem h
    refine ⟨(a₂ * a₁) * x * (a₁ * a₂),
      K.mul_mem (K.mul_mem (K.mul_mem h2 h1) hxK) (K.mul_mem h1 h2), ?_⟩
    rw [zs4h_toMatrix_mul, zs4h_toMatrix_mul, zs4h_toMatrix_a2a1 h, hx, zs4h_toMatrix_a1a2 h,
      zs4h_diag_pij02 (Units.ne_zero lam), pow_succ']

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_centre_sq (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) {z : U ≃ₗ[ZMod p] U}
    (hz : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, z v = -v)
    (hz' : ∀ v ∈ centralizerSpace F, z v = v) : z * z = 1 := by
  ext v
  have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
    rw [h.splitSupport_F.1.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  simp [LinearEquiv.mul_apply, map_add, hz a ha, hz' b hb]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_repr_apply (f : Module.Basis (Fin 4) (ZMod p) U) (x : U ≃ₗ[ZMod p] U) (v : U)
    (i : Fin 4) : f.repr (x v) i =
      ∑ j, LinearMap.toMatrix f f x.toLinearMap i j * f.repr v j := by
  have h := congrFun (LinearMap.toMatrix_mulVec_repr f f x.toLinearMap v) i
  simpa [Matrix.mulVec, dotProduct] using h.symm

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_Z_exists (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) {z : U ≃ₗ[ZMod p] U}
    (hzF : z ∈ F) (hzc : ∀ x ∈ F, z * x = x * z)
    (hz : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, z v = -v)
    (hz' : ∀ v ∈ centralizerSpace F, z v = v) :
    ∃ a b c d : ZMod p, LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] := by
  refine ⟨LinearMap.toMatrix f f z.toLinearMap 2 2, LinearMap.toMatrix f f z.toLinearMap 2 3,
    LinearMap.toMatrix f f z.toLinearMap 3 2, LinearMap.toMatrix f f z.toLinearMap 3 3, ?_⟩
  ext i j
  by_cases hij : i.val < 2 ∨ j.val < 2
  · rw [toMatrix_centre_block h hzF hzc hz hz' i j hij]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · rw [not_or, not_lt, not_lt] at hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢

private lemma zs4h_Z_sq {a b c d : ZMod p}
    (h : (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) (ZMod p)) *
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] = 1) :
    a * a + b * c = 1 ∧ a * b + b * d = 0 ∧ c * a + d * c = 0 ∧ c * b + d * d = 1 := by
  have h22 := congrFun (congrFun h 2) 2
  have h23 := congrFun (congrFun h 2) 3
  have h32 := congrFun (congrFun h 3) 2
  have h33 := congrFun (congrFun h 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at h22 h23 h32 h33
  exact ⟨h22, h23, h32, h33⟩

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_K_invariant (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {W : Submodule (ZMod p) U} (h₁ : ∀ w ∈ W, a₁ w ∈ W) (h₂ : ∀ w ∈ W, a₂ w ∈ W)
    (h₃ : ∀ w ∈ W, a₃ w ∈ W) (hF : ∀ k ∈ F, ∀ w ∈ W, k w ∈ W) :
    ∀ k ∈ K, ∀ w ∈ W, k w ∈ W := by
  obtain ⟨r₁, r₂, r₃⟩ := zs4h_refl_gens h
  intro k hk
  rw [h.eq_K, ← Subgroup.closure_eq F, ← Subgroup.closure_union] at hk
  induction hk using Subgroup.closure_induction'' with
  | mem g hg =>
    intro w hw
    rcases hg with hg | hg
    · rcases hg with rfl | rfl | rfl
      · exact h₁ w hw
      · exact h₂ w hw
      · exact h₃ w hw
    · exact hF g hg w hw
  | inv_mem g hg =>
    intro w hw
    rcases hg with hg | hg
    · rcases hg with rfl | rfl | rfl
      · rw [inv_eq_of_mul_eq_one_right r₁.1]; exact h₁ w hw
      · rw [inv_eq_of_mul_eq_one_right r₂.1]; exact h₂ w hw
      · rw [inv_eq_of_mul_eq_one_right r₃.1]; exact h₃ w hw
    · exact hF g⁻¹ (F.inv_mem hg) w hw
  | one => intro w hw; simpa using hw
  | mul x y _ _ ihx ihy => intro w hw; exact ihx (y w) (ihy w hw)

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_centralizer_ne_bot (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) :
    centralizerSpace F ≠ ⊥ := by
  intro hbot
  have htop := h.splitSupport_F.1.sup_eq_top
  rw [hbot, sup_bot_eq] at htop
  have h3 := h.splitSupport_F.2.1
  rw [htop, finrank_top, Module.finrank_eq_card_basis f] at h3
  simp at h3

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_ev_coords {z : U ≃ₗ[ZMod p] U} {b d : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, b; 0, 0, 0, d]) (v : U) :
    f.repr (z v) 0 = -f.repr v 0 ∧ f.repr (z v) 1 = -f.repr v 1 ∧
      f.repr (z v) 2 = -f.repr v 2 + b * f.repr v 3 ∧ f.repr (z v) 3 = d * f.repr v 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [zs4h_repr_apply, hZ] <;> simp [Fin.sum_univ_four]

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_ev_ker (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) {z : U ≃ₗ[ZMod p] U}
    (hz' : ∀ v ∈ centralizerSpace F, z v = v) {b d : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, b; 0, 0, 0, d]) {v : U} (hv : z v = -v) :
    f.repr v 3 = 0 := by
  have h2 := zs4h_two_ne_zero (zs4h_p_ne_two h)
  by_contra hv3
  obtain ⟨-, -, c2, c3⟩ := zs4h_ev_coords hZ v
  have e2 : b * f.repr v 3 = 0 := by
    have := congrArg (fun w => f.repr w 2) hv
    simp only [c2, map_neg, Finsupp.neg_apply] at this
    linear_combination this
  have e3 : (d + 1) * f.repr v 3 = 0 := by
    have := congrArg (fun w => f.repr w 3) hv
    simp only [c3, map_neg, Finsupp.neg_apply] at this
    linear_combination this
  have hb : b = 0 := (mul_eq_zero.mp e2).resolve_right hv3
  have hd : d = -1 := by
    have := (mul_eq_zero.mp e3).resolve_right hv3
    linear_combination this
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (zs4h_centralizer_ne_bot h)
  have hzu : z u = -u := by
    apply f.repr.injective
    ext i
    obtain ⟨c0, c1, c2, c3⟩ := zs4h_ev_coords hZ u
    fin_cases i <;> simp [c0, c1, c2, c3, hb, hd]
  have hneg : -u = u := hzu.symm.trans (hz' u hu)
  have h2u : (2 : ZMod p) • u = 0 := by
    rw [two_smul]
    calc u + u = u + -u := by rw [hneg]
      _ = 0 := add_neg_cancel u
  exact hu0 ((smul_eq_zero.mp h2u).resolve_left h2)

private lemma zs4h_pij_row3 {i j : Fin 4} (hi : i ≠ 3) (hj : j ≠ 3) (α : ZMod p) (c : Fin 4) :
    pijMat i j α 3 c = if c = 3 then 1 else 0 := by
  simp only [pijMat]
  by_cases hc : c = 3
  · subst hc; simp [Ne.symm hi, Ne.symm hj]
  · simp [hc, Ne.symm hi, Ne.symm hj, Ne.symm hc]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_repr3_pij {x : U ≃ₗ[ZMod p] U} {i j : Fin 4} (hi : i ≠ 3) (hj : j ≠ 3)
    {α : ZMod p} (hx : LinearMap.toMatrix f f x.toLinearMap = pijMat i j α) (w : U) :
    f.repr (x w) 3 = f.repr w 3 := by
  rw [zs4h_repr_apply, hx, Fin.sum_univ_four]
  simp [zs4h_pij_row3 hi hj]

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_false_of_Z22_neg (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzc : ∀ x ∈ F, z * x = x * z)
    (hz' : ∀ v ∈ centralizerSpace F, z v = v) {b d : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, b; 0, 0, 0, d]) : False := by
  set W : Submodule (ZMod p) U := LinearMap.ker (f.coord 3) with hW
  have hmem : ∀ v, v ∈ W ↔ f.repr v 3 = 0 := fun v => by
    simp [hW, LinearMap.mem_ker, Module.Basis.coord_apply]
  have hzW : ∀ w ∈ W, z w = -w := by
    intro w hw
    have hw3 := (hmem w).mp hw
    obtain ⟨c0, c1, c2, c3⟩ := zs4h_ev_coords hZ w
    apply f.repr.injective
    ext i
    fin_cases i <;> simp [c0, c1, c2, c3, hw3]
  have hF : ∀ k ∈ F, ∀ w ∈ W, k w ∈ W := by
    intro k hk w hw
    rw [hmem]
    refine zs4h_ev_ker h hz' hZ ?_
    rw [← LinearEquiv.mul_apply, hzc k hk, LinearEquiv.mul_apply, hzW w hw, map_neg]
  have hinv := zs4h_K_invariant h
    (fun w hw => (hmem _).mpr (by
      rw [zs4h_repr3_pij (by decide) (by decide) h.toMatrix_a₁]; exact (hmem w).mp hw))
    (fun w hw => (hmem _).mpr (by
      rw [zs4h_repr3_pij (by decide) (by decide) h.toMatrix_a₂]; exact (hmem w).mp hw))
    (fun w hw => (hmem _).mpr (by
      rw [zs4h_repr3_pij (by decide) (by decide) h.toMatrix_a₃]; exact (hmem w).mp hw)) hF
  rcases h.irred W hinv with hbot | htop
  · have h0 : f 0 ∈ W := (hmem _).mpr (by simp)
    rw [hbot] at h0
    exact f.ne_zero 0 ((Submodule.mem_bot _).mp h0)
  · have h3 : f 3 ∈ W := htop ▸ Submodule.mem_top
    have := (hmem _).mp h3
    simp at this

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_lam_facts (hlam : orderOf lam = 5) :
    (lam : ZMod p) ≠ 0 ∧ (lam : ZMod p) ≠ 1 ∧ (lam : ZMod p) ^ 5 = 1 ∧
      (lam : ZMod p) ^ 4 + (lam : ZMod p) ^ 3 + (lam : ZMod p) ^ 2 + (lam : ZMod p) + 1 = 0 := by
  have h5 : (lam : ZMod p) ^ 5 = 1 := by
    have := pow_orderOf_eq_one lam
    rw [hlam] at this
    simpa using congrArg Units.val this
  have h1 : (lam : ZMod p) ≠ 1 := by
    intro hh
    have : lam = 1 := Units.ext hh
    rw [this, orderOf_one] at hlam
    omega
  refine ⟨Units.ne_zero lam, h1, h5, ?_⟩
  have : ((lam : ZMod p) - 1) * ((lam : ZMod p) ^ 4 + (lam : ZMod p) ^ 3 + (lam : ZMod p) ^ 2 +
      (lam : ZMod p) + 1) = 0 := by linear_combination h5
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_lam_pow_ne_one (hlam : orderOf lam = 5) {k : ℕ} (hk0 : 0 < k) (hk : k < 5) :
    (lam : ZMod p) ^ k ≠ 1 := by
  intro hh
  have : lam ^ k = 1 := Units.ext (by simpa using hh)
  have := orderOf_le_of_pow_eq_one hk0 this
  omega

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_rho_exists (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) {z : U ≃ₗ[ZMod p] U}
    (hzK : z ∈ K) (hzz : z * z = 1) {a b c d : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d]) :
    ∃ ρ ∈ K, IsRefl p ρ ∧ LinearMap.toMatrix f f ρ.toLinearMap =
      1 - Matrix.vecMulVec ![0, -1, -a, -c] ![0, -1, -a, -b] := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hZZ : (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] :
      Matrix (Fin 4) (Fin 4) (ZMod p)) * !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] =
      1 := by
    rw [← hZ, ← zs4h_toMatrix_mul, hzz]; simp
  refine ⟨z * a₃ * z⁻¹, K.mul_mem (K.mul_mem hzK (zs4h_gens_mem h).2.2) (K.inv_mem hzK),
    IsRefl.conj (zs4h_refl_gens h).2.2 z, ?_⟩
  have hP : pijMat (1 : Fin 4) 2 (1 : ZMod p) =
      1 - Matrix.vecMulVec ![0, 1, -1, 0] ![0, 1, -1, 0] := by
    have := zs4h_pij12_eq (1 : ZMod p) one_ne_zero
    rwa [inv_one] at this
  have hmv : (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] :
      Matrix (Fin 4) (Fin 4) (ZMod p)).mulVec ![0, 1, -1, 0] = ![0, -1, -a, -c] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have hvm : (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] :
      Matrix (Fin 4) (Fin 4) (ZMod p)).vecMul ![0, 1, -1, 0] = ![0, -1, -a, -b] := by
    ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_four]
  rw [hzinv, zs4h_toMatrix_mul, zs4h_toMatrix_mul, hZ, h.toMatrix_a₃,
    zs4h_conj_refl hZZ hP, hmv, hvm]

private lemma zs4h_dep_of_sq {a b c η : ZMod p} (hη : η ≠ 0) (hne : η * η ≠ 1)
    (hB : a * a + b * c = 1) : ¬ (c = 0 ∧ a = -η⁻¹) := by
  rintro ⟨hc, ha⟩
  apply hne
  have h1 : η⁻¹ * η⁻¹ = 1 := by
    rw [ha, hc] at hB
    linear_combination hB
  linear_combination (-(η * η)) * h1 + (η * η⁻¹ + 1) * (mul_inv_cancel₀ hη)

private theorem zs4h_nm_p1 (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzK : z ∈ K) (hzz : z * z = 1) {a b c d : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d]) (hB : a * a + b * c = 1) :
    a = 0 ∨ (a ^ 2 - 1) * (a ^ 2 - 2) * ((a ^ 2) ^ 2 - 3 * a ^ 2 + 1) = 0 := by
  obtain ⟨ρ, hρK, hρr, hρ⟩ := zs4h_rho_exists h hzK hzz hZ
  obtain ⟨x, hxK, hx⟩ := zs4h_mem_pij02 h 0
  rw [pow_zero] at hx
  have hxr : IsRefl p x := isRefl_of_toMatrix_eq_pijMat f (by decide) one_ne_zero hx
  have hS : LinearMap.toMatrix f f x.toLinearMap =
      1 - Matrix.vecMulVec ![1, 0, -1, 0] ![1, 0, -1, 0] := by
    rw [hx, zs4h_pij02_eq 1 one_ne_zero, inv_one]
  have e1 : dotProduct ![1, 0, -1, 0] ![0, -1, -a, -c] = a := by
    simp [dotProduct, Fin.sum_univ_four]
  have e2 : dotProduct ![0, -1, -a, -b] ![1, 0, -1, 0] = a := by
    simp [dotProduct, Fin.sum_univ_four]
  have key := zs4h_pair hp h hxK hρK hxr hρr hS hρ
    (by simp [dotProduct, Fin.sum_univ_four]; norm_num)
    (by simp [dotProduct, Fin.sum_univ_four]; linear_combination hB) ?_
  · rw [e1, e2] at key
    rcases key with ⟨h1, -⟩ | h2
    · exact Or.inl h1
    · exact Or.inr (by linear_combination h2)
  · intro α β hαβ
    have c0 : α * 1 + β * 0 = 0 := congrFun hαβ 0
    have c1 : α * 0 + β * (-1) = 0 := congrFun hαβ 1
    exact ⟨by linear_combination c0, by linear_combination -c1⟩

private theorem zs4h_nm_k (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzK : z ∈ K) (hzz : z * z = 1) {a b c d : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d]) (hB : a * a + b * c = 1)
    {η t : ZMod p} (hη : η ≠ 0) (ht : t = η + η⁻¹)
    (hx : ∃ x ∈ K, LinearMap.toMatrix f f x.toLinearMap = pijMat 1 2 η)
    (hdep : ¬ (c = 0 ∧ a = -η⁻¹)) :
    (η * η = 1 ∧ a = η) ∨ (a ^ 2 - a * t + 1 - 1) * (a ^ 2 - a * t + 1 - 2) *
      ((a ^ 2 - a * t + 1) ^ 2 - 3 * (a ^ 2 - a * t + 1) + 1) = 0 := by
  obtain ⟨ρ, hρK, hρr, hρ⟩ := zs4h_rho_exists h hzK hzz hZ
  obtain ⟨x, hxK, hx⟩ := hx
  have hxr : IsRefl p x := isRefl_of_toMatrix_eq_pijMat f (by decide) hη hx
  have hS : LinearMap.toMatrix f f x.toLinearMap =
      1 - Matrix.vecMulVec ![0, 1, -η⁻¹, 0] ![0, 1, -η, 0] := by
    rw [hx, zs4h_pij12_eq η hη]
  have hinv : η * η⁻¹ = 1 := mul_inv_cancel₀ hη
  have e1 : dotProduct ![0, 1, -η, 0] ![0, -1, -a, -c] = -1 + η * a := by
    simp [dotProduct, Fin.sum_univ_four]
  have e2 : dotProduct ![0, -1, -a, -b] ![0, 1, -η⁻¹, 0] = -1 + a * η⁻¹ := by
    simp [dotProduct, Fin.sum_univ_four]
  have key := zs4h_pair hp h hxK hρK hxr hρr hS hρ
    (by simp [dotProduct, Fin.sum_univ_four]; linear_combination hinv)
    (by simp [dotProduct, Fin.sum_univ_four]; linear_combination hB) ?_
  · rw [e1, e2] at key
    rcases key with ⟨h1, h2⟩ | h3
    · have ha : a = η := by linear_combination η * h2 - a * hinv
      exact Or.inl ⟨by linear_combination h1 - η * ha, ha⟩
    · have eκ : (-1 + η * a) * (-1 + a * η⁻¹) = a ^ 2 - a * t + 1 := by
        rw [ht]
        linear_combination a ^ 2 * hinv
      rw [eκ] at h3
      exact Or.inr h3
  · intro α β hαβ
    have c1 : α * 1 + β * (-1) = 0 := congrFun hαβ 1
    have c2 : α * (-η⁻¹) + β * (-a) = 0 := congrFun hαβ 2
    have c3 : α * 0 + β * (-c) = 0 := congrFun hαβ 3
    have hβ : β = 0 := by
      by_contra hβ0
      apply hdep
      have hc : c = 0 := (mul_eq_zero.mp (by linear_combination -c3 : β * c = 0)).resolve_left hβ0
      refine ⟨hc, ?_⟩
      have h4 : β * (a + η⁻¹) = 0 := by linear_combination -c2 - η⁻¹ * c1
      have h5 := (mul_eq_zero.mp h4).resolve_left hβ0
      linear_combination h5
    exact ⟨by linear_combination c1 + hβ, hβ⟩

private theorem zs4h_nm_rel1 (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzK : z ∈ K) (hzz : z * z = 1) {a b c d s : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d]) (hB : a * a + b * c = 1)
    (hs : s = (lam : ZMod p) + (lam : ZMod p)⁻¹) :
    (a ^ 2 - a * s + 1 - 1) * (a ^ 2 - a * s + 1 - 2) *
      ((a ^ 2 - a * s + 1) ^ 2 - 3 * (a ^ 2 - a * s + 1) + 1) = 0 := by
  have hl0 : (lam : ZMod p) ≠ 0 := Units.ne_zero lam
  have hne : (lam : ZMod p) * lam ≠ 1 := by
    rw [← sq]
    exact zs4h_lam_pow_ne_one h.orderOf_lam (by norm_num) (by norm_num)
  rcases zs4h_nm_k hp h hzK hzz hZ hB hl0 hs (by simpa using zs4h_mem_pij12 h 1)
    (zs4h_dep_of_sq hl0 hne hB) with ⟨h1, -⟩ | h2
  · exact absurd h1 hne
  · exact h2

private theorem zs4h_nm_rel2 (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzK : z ∈ K) (hzz : z * z = 1) {a b c d s : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d]) (hB : a * a + b * c = 1)
    (hs : s = (lam : ZMod p) + (lam : ZMod p)⁻¹) (hss : s * s + s - 1 = 0) :
    (a ^ 2 - a * (-1 - s) + 1 - 1) * (a ^ 2 - a * (-1 - s) + 1 - 2) *
      ((a ^ 2 - a * (-1 - s) + 1) ^ 2 - 3 * (a ^ 2 - a * (-1 - s) + 1) + 1) = 0 := by
  have hl0 : (lam : ZMod p) ≠ 0 := Units.ne_zero lam
  have hne : (lam : ZMod p) ^ 2 * (lam : ZMod p) ^ 2 ≠ 1 := by
    rw [← pow_add]
    exact zs4h_lam_pow_ne_one h.orderOf_lam (by norm_num) (by norm_num)
  have hη : (lam : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hl0
  have ht : -1 - s = (lam : ZMod p) ^ 2 + ((lam : ZMod p) ^ 2)⁻¹ := by
    rw [hs]
    exact (zs4h_t2_rel hl0 (by rw [← hs]; exact hss)).symm
  rcases zs4h_nm_k hp h hzK hzz hZ hB hη ht (zs4h_mem_pij12 h 2)
    (zs4h_dep_of_sq hη hne hB) with ⟨h1, -⟩ | h2
  · exact absurd h1 hne
  · exact h2

private theorem zs4h_nm_rel0 (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzK : z ∈ K) (hzz : z * z = 1) {a b c d : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d]) (hB : a * a + b * c = 1)
    (hc0 : ¬ (c = 0 ∧ a = -1)) :
    a = 1 ∨ (a ^ 2 - a * 2 + 1 - 1) * (a ^ 2 - a * 2 + 1 - 2) *
      ((a ^ 2 - a * 2 + 1) ^ 2 - 3 * (a ^ 2 - a * 2 + 1) + 1) = 0 := by
  rcases zs4h_nm_k hp h hzK hzz hZ hB (η := 1) (t := 2) one_ne_zero (by norm_num)
    (by simpa using zs4h_mem_pij12 h 0) (by simpa using hc0) with ⟨-, h1⟩ | h2
  · exact Or.inl h1
  · exact Or.inr h2

private theorem zs4h_Z22 (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzK : z ∈ K) (hzz : z * z = 1) (hzc : ∀ x ∈ F, z * x = x * z)
    (hz' : ∀ v ∈ centralizerSpace F, z v = v) {a b c d : ZMod p}
    (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d]) (hB : a * a + b * c = 1) :
    a = 0 := by
  by_contra ha
  obtain ⟨hl0, -, -, hΦ⟩ := zs4h_lam_facts h.orderOf_lam
  obtain ⟨h3, h5, h37⟩ := zs4h_p_facts h.orderOf_lam
  have h2 := zs4h_two_ne_zero hp
  obtain ⟨s, hsdef⟩ : ∃ s : ZMod p, s = (lam : ZMod p) + (lam : ZMod p)⁻¹ := ⟨_, rfl⟩
  have hs : s * s + s - 1 = 0 := by rw [hsdef]; exact zs4h_s_rel hl0 hΦ
  have hr1 := zs4h_nm_rel1 hp h hzK hzz hZ hB hsdef
  by_cases ha1 : a = 1
  · exact zs4h_alg_a1 hs h2 ha1 hr1
  have hc0 : ¬ (c = 0 ∧ a = -1) := by
    rintro ⟨hc, ha'⟩
    subst hc ha'
    exact zs4h_false_of_Z22_neg h hzc hz' hZ
  exact zs4h_alg_cancel hs ha h2 h3 h5 h37 rfl rfl rfl
    ((zs4h_nm_p1 hp h hzK hzz hZ hB).resolve_left ha)
    ((zs4h_nm_rel0 hp h hzK hzz hZ hB hc0).resolve_left ha1) hr1
    (zs4h_nm_rel2 hp h hzK hzz hZ hB hsdef hs)

private lemma zs4h_pij_col3 {i j : Fin 4} (hi : i ≠ 3) (hj : j ≠ 3) (α : ZMod p) (r : Fin 4) :
    pijMat i j α r 3 = if r = 3 then 1 else 0 := by
  simp only [pijMat]
  by_cases hr : r = 3
  · subst hr; simp [Ne.symm hi, Ne.symm hj]
  · simp [hr, Ne.symm hi, Ne.symm hj]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_toMatrix_unitsSMul (f : Module.Basis (Fin 4) (ZMod p) U)
    (w : Fin 4 → (ZMod p)ˣ) (x : U ≃ₗ[ZMod p] U) (i j : Fin 4) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) x.toLinearMap i j =
      ((w i)⁻¹ : (ZMod p)ˣ) * LinearMap.toMatrix f f x.toLinearMap i j * (w j : ZMod p) := by
  simp only [LinearMap.toMatrix_apply, Module.Basis.repr_unitsSMul, Module.Basis.unitsSMul_apply,
    Units.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_rescale_pij {i j : Fin 4} (hi : i ≠ 3) (hj : j ≠ 3) {α : ZMod p}
    {x : U ≃ₗ[ZMod p] U} (hx : LinearMap.toMatrix f f x.toLinearMap = pijMat i j α)
    (c : (ZMod p)ˣ) :
    LinearMap.toMatrix (f.unitsSMul ![1, 1, 1, c]) (f.unitsSMul ![1, 1, 1, c])
      x.toLinearMap = pijMat i j α := by
  ext r s
  rw [zs4h_toMatrix_unitsSMul, hx]
  have hw : ∀ r : Fin 4, r ≠ 3 → (![1, 1, 1, c] r) = 1 := by
    intro r hr
    fin_cases r <;> first | rfl | exact absurd rfl hr
  by_cases hr : r = 3
  · subst hr
    by_cases hs : s = 3
    · subst hs
      rw [zs4h_pij_row3 hi hj, if_pos rfl]
      show ((c⁻¹ : (ZMod p)ˣ) : ZMod p) * 1 * (c : ZMod p) = 1
      rw [mul_one]
      exact c.inv_mul
    · rw [zs4h_pij_row3 hi hj, if_neg hs, mul_zero, zero_mul]
  · by_cases hs : s = 3
    · subst hs
      rw [zs4h_pij_col3 hi hj, if_neg hr, mul_zero, zero_mul]
    · rw [hw r hr, hw s hs]
      simp

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_rescale_centre {z : U ≃ₗ[ZMod p] U} {b c : ZMod p} (hbc : b * c = 1)
    (hb : b ≠ 0) (hZ : LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 0, b; 0, 0, c, 0]) :
    LinearMap.toMatrix (f.unitsSMul ![1, 1, 1, Units.mk0 (-b⁻¹) (by simp [hb])])
      (f.unitsSMul ![1, 1, 1, Units.mk0 (-b⁻¹) (by simp [hb])]) z.toLinearMap =
      -pijMat 2 3 1 := by
  ext r s
  rw [zs4h_toMatrix_unitsSMul, hZ]
  fin_cases r <;> fin_cases s <;> simp [pijMat, hb, hbc]

omit [Module.Finite (ZMod p) U] in
private theorem zs4h_rescale_data (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) (c : (ZMod p)ˣ) :
    FourThreeData (f.unitsSMul ![1, 1, 1, c]) lam a₁ a₂ a₃ a₄ K F :=
  ⟨h.orderOf_lam, zs4h_rescale_pij (by decide) (by decide) h.toMatrix_a₁ c,
    zs4h_rescale_pij (by decide) (by decide) h.toMatrix_a₂ c,
    zs4h_rescale_pij (by decide) (by decide) h.toMatrix_a₃ c, h.isRefl_a₄, h.eq_K, h.irred,
    h.transvectionFree, h.dmax, h.a₁_mem, h.a₂_mem, h.a₄_mem, h.splitSupport_F, h.h3,
    h.splitOfIrred, h.noOrth, h.negOfPrim⟩

private theorem zs4h_Z_anti (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzF : z ∈ F) (hzc : ∀ x ∈ F, z * x = x * z)
    (hz : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, z v = -v)
    (hz' : ∀ v ∈ centralizerSpace F, z v = v) :
    ∃ b c : ZMod p, b * c = 1 ∧ LinearMap.toMatrix f f z.toLinearMap =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 0, b; 0, 0, c, 0] := by
  obtain ⟨a, b, c, d, hZ⟩ := zs4h_Z_exists h hzF hzc hz hz'
  have hzz := zs4h_centre_sq h hz hz'
  have hZZ : (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] :
      Matrix (Fin 4) (Fin 4) (ZMod p)) * !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, a, b; 0, 0, c, d] =
      1 := by
    rw [← hZ, ← zs4h_toMatrix_mul, hzz]; simp
  obtain ⟨e1, e2, -, -⟩ := zs4h_Z_sq hZZ
  have hzK : z ∈ K := by rw [h.eq_K]; exact Subgroup.mem_sup_right hzF
  have ha : a = 0 := zs4h_Z22 hp h hzK hzz hzc hz' hZ e1
  subst ha
  have hbc : b * c = 1 := by linear_combination e1
  have hb : b ≠ 0 := left_ne_zero_of_mul_eq_one hbc
  have hd : d = 0 := (mul_eq_zero.mp (by linear_combination e2 : b * d = 0)).resolve_left hb
  subst hd
  exact ⟨b, c, hbc, hZ⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_comm_of_orderOf_two {x y : U ≃ₗ[ZMod p] U} (hx : x * x = 1) (hy : y * y = 1)
    (h : orderOf (x * y) = 2) : x * y = y * x := by
  have h1 : (x * y) * (x * y) = 1 := by
    have := pow_orderOf_eq_one (x * y)
    rwa [h, sq] at this
  have e1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy] at e1
  exact e1.symm

private lemma zs4h_fin_uw {x u w τ ν : ZMod p} (h2 : (2 : ZMod p) ≠ 0) (hxν : x = 1 + ν)
    (hτν : τ * ν = 1)
    (hmul : (!![x, x - 1, w, w; x - 1, x, w, w; u, u, 1 - x, -x; u, u, -x, 1 - x] :
      Matrix (Fin 4) (Fin 4) (ZMod p)) *
      !![x, x - 1, w, w; x - 1, x, w, w; u, u, 1 - x, -x; u, u, -x, 1 - x] = 1) :
    u * w * τ = -(1 + ν) := by
  have h00 := congrFun (congrFun hmul 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four] at h00
  have h0 : 2 * (u * w - x * (1 - x)) = 0 := by linear_combination h00
  have huw : u * w - x * (1 - x) = 0 := (mul_eq_zero.mp h0).resolve_left h2
  linear_combination τ * huw - τ * (x + ν) * hxν - (1 + ν) * hτν

private lemma zs4h_fin_S4 {x u w τ ν : ZMod p} (hxν : x = 1 + ν) (hτν : τ * ν = 1)
    (huwτ : u * w * τ = -(1 + ν)) :
    (!![x, x - 1, w, w; x - 1, x, w, w; u, u, 1 - x, -x; u, u, -x, 1 - x] :
      Matrix (Fin 4) (Fin 4) (ZMod p)) =
      1 - Matrix.vecMulVec ![-1, -1, -u * τ, -u * τ] ![ν, ν, w, w] := by
  subst hxν
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | ring1 | linear_combination (-u) * hτν | linear_combination u * hτν |
      linear_combination (-1) * huwτ

private lemma zs4h_fin_alt {s τ ν u w ζ : ZMod p} (hτ : τ = s - 2) (hss : s * s + s - 1 = 0)
    (hτν : τ * ν = 1) (huwτ : u * w * τ = -(1 + ν)) (hζ : ζ ≠ 0)
    (h1 : -1 + ζ * u * τ = 0) (h2 : ν - w * ζ⁻¹ = 0) : False := by
  have hinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ
  have e1 : u * w * τ = ν := by
    linear_combination (-(u * w * τ)) * hinv + (w * ζ⁻¹) * h1 - h2
  have e2 : 2 * ν + 1 = 0 := by linear_combination huwτ - e1
  have e3 : τ + 2 = 0 := by linear_combination τ * e2 - 2 * hτν
  have e4 : s = 0 := by linear_combination e3 - hτ
  have : (1 : ZMod p) = 0 := by linear_combination -hss + (s + 1) * e4
  exact one_ne_zero this

private lemma zs4h_lam_inv {l : ZMod p} (hl5 : l ^ 5 = 1) (k m : ℕ) (hkm : k + m = 5) :
    (l ^ k)⁻¹ = l ^ m :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_add, hkm, hl5])

private theorem zs4h_fin_pair (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {τ ν u w ζ : ZMod p} (hτν : τ * ν = 1) (huwτ : u * w * τ = -(1 + ν)) (hζ : ζ ≠ 0)
    (hx : ∃ x ∈ K, LinearMap.toMatrix f f x.toLinearMap = pijMat 0 2 ζ)
    (hS4 : LinearMap.toMatrix f f a₄.toLinearMap =
      1 - Matrix.vecMulVec ![-1, -1, -u * τ, -u * τ] ![ν, ν, w, w]) :
    (-1 + ζ * u * τ = 0 ∧ ν - w * ζ⁻¹ = 0) ∨
      (ζ * u + ζ⁻¹ * w) * ((ζ * u + ζ⁻¹ * w) - 1) *
        ((ζ * u + ζ⁻¹ * w) ^ 2 - (ζ * u + ζ⁻¹ * w) - 1) = 0 := by
  obtain ⟨x, hxK, hx⟩ := hx
  have ha4K : a₄ ∈ K := by rw [h.eq_K]; exact Subgroup.mem_sup_right h.a₄_mem
  have hxr : IsRefl p x := isRefl_of_toMatrix_eq_pijMat f (by decide) hζ hx
  have hS : LinearMap.toMatrix f f x.toLinearMap =
      1 - Matrix.vecMulVec ![1, 0, -ζ⁻¹, 0] ![1, 0, -ζ, 0] := by
    rw [hx, zs4h_pij02_eq ζ hζ]
  have hinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ
  have e1 : dotProduct ![1, 0, -ζ, 0] ![-1, -1, -u * τ, -u * τ] = -1 + ζ * u * τ := by
    simp [dotProduct, Fin.sum_univ_four]; ring
  have e2 : dotProduct ![ν, ν, w, w] ![1, 0, -ζ⁻¹, 0] = ν - w * ζ⁻¹ := by
    simp [dotProduct, Fin.sum_univ_four]; ring
  have key := zs4h_pair hp h hxK ha4K hxr h.isRefl_a₄ hS hS4
    (by simp [dotProduct, Fin.sum_univ_four]; linear_combination hinv)
    (by simp [dotProduct, Fin.sum_univ_four]; linear_combination (-2) * huwτ) ?_
  · rw [e1, e2] at key
    rcases key with h1 | h3
    · exact Or.inl h1
    · have eκ : (-1 + ζ * u * τ) * (ν - w * ζ⁻¹) = (ζ * u + ζ⁻¹ * w) + 1 := by
        linear_combination (ζ * u) * hτν - huwτ - (u * w * τ) * hinv
      rw [eκ] at h3
      exact Or.inr (by linear_combination h3)
  · intro α β hαβ
    have c0 : α * 1 + β * (-1) = 0 := congrFun hαβ 0
    have c1 : α * 0 + β * (-1) = 0 := congrFun hαβ 1
    exact ⟨by linear_combination c0 - c1, by linear_combination -c1⟩

private theorem zs4h_fin_sum (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {s τ ν u w : ZMod p} (hs : s = (lam : ZMod p) + (lam : ZMod p)⁻¹) (hτ : τ = s - 2)
    (hτν : τ * ν = 1) (huwτ : u * w * τ = -(1 + ν))
    (hS4 : LinearMap.toMatrix f f a₄.toLinearMap =
      1 - Matrix.vecMulVec ![-1, -1, -u * τ, -u * τ] ![ν, ν, w, w]) : False := by
  obtain ⟨hl0, -, hl5, hΦ⟩ := zs4h_lam_facts h.orderOf_lam
  obtain ⟨h3, h5, -⟩ := zs4h_p_facts h.orderOf_lam
  have h2 := zs4h_two_ne_zero hp
  have hss : s * s + s - 1 = 0 := by rw [hs]; exact zs4h_s_rel hl0 hΦ
  have hR : ∀ k : ℕ, ((lam : ZMod p) ^ k * u + ((lam : ZMod p) ^ k)⁻¹ * w) *
      (((lam : ZMod p) ^ k * u + ((lam : ZMod p) ^ k)⁻¹ * w) - 1) *
      (((lam : ZMod p) ^ k * u + ((lam : ZMod p) ^ k)⁻¹ * w) ^ 2 -
        ((lam : ZMod p) ^ k * u + ((lam : ZMod p) ^ k)⁻¹ * w) - 1) = 0 := fun k =>
    (zs4h_fin_pair hp h hτν huwτ (pow_ne_zero k hl0) (zs4h_mem_pij02 h k) hS4).resolve_left
      (fun hh => zs4h_fin_alt hτ hss hτν huwτ (pow_ne_zero k hl0) hh.1 hh.2)
  have hsum := zs4h_alg_sum hΦ
    (by simp : (lam : ZMod p) ^ 0 * u + ((lam : ZMod p) ^ 0)⁻¹ * w = u + w)
    (by rw [zs4h_lam_inv hl5 1 4 rfl]; ring :
      (lam : ZMod p) ^ 1 * u + ((lam : ZMod p) ^ 1)⁻¹ * w = lam * u + lam ^ 4 * w)
    (by rw [zs4h_lam_inv hl5 2 3 rfl] :
      (lam : ZMod p) ^ 2 * u + ((lam : ZMod p) ^ 2)⁻¹ * w = lam ^ 2 * u + lam ^ 3 * w)
    (by rw [zs4h_lam_inv hl5 3 2 rfl] :
      (lam : ZMod p) ^ 3 * u + ((lam : ZMod p) ^ 3)⁻¹ * w = lam ^ 3 * u + lam ^ 2 * w)
    (by rw [zs4h_lam_inv hl5 4 1 rfl]; ring :
      (lam : ZMod p) ^ 4 * u + ((lam : ZMod p) ^ 4)⁻¹ * w = lam ^ 4 * u + lam * w)
    (hR 0) (hR 1) (hR 2) (hR 3) (hR 4)
  have h30 : (30 : ZMod p) ≠ 0 := by
    have : (30 : ZMod p) = 2 * 3 * 5 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero h2 h3) h5
  have huw0 : u * w = 0 :=
    (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hsum).resolve_left h30)
  have e5 : 1 + ν = 0 := by linear_combination huwτ - τ * huw0
  have e6 : τ + 1 = 0 := by linear_combination τ * e5 - hτν
  have e7 : s = 1 := by linear_combination e6 - hτ
  exact one_ne_zero (by linear_combination hss - (s + 2) * e7 : (1 : ZMod p) = 0)

private theorem zs4h_final_core (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {x u w s : ZMod p} (hs : s = (lam : ZMod p) + ((lam⁻¹ : (ZMod p)ˣ) : ZMod p))
    (hx : x = (s - 1) / (s - 2))
    (hM : LinearMap.toMatrix f f a₄.toLinearMap =
      !![x, x - 1, w, w; x - 1, x, w, w; u, u, 1 - x, -x; u, u, -x, 1 - x]) : False := by
  obtain ⟨hl0, -, -, hΦ⟩ := zs4h_lam_facts h.orderOf_lam
  obtain ⟨-, h5, -⟩ := zs4h_p_facts h.orderOf_lam
  rw [Units.val_inv_eq_inv_val] at hs
  have hss : s * s + s - 1 = 0 := by rw [hs]; exact zs4h_s_rel hl0 hΦ
  obtain ⟨τ, hτ⟩ : ∃ τ : ZMod p, τ = s - 2 := ⟨_, rfl⟩
  have hτ0 : τ ≠ 0 := by
    intro h0
    apply h5
    have hs2 : s = 2 := by linear_combination h0 - hτ
    rw [hs2] at hss
    linear_combination hss
  obtain ⟨ν, hν⟩ : ∃ ν : ZMod p, ν = τ⁻¹ := ⟨_, rfl⟩
  have hτν : τ * ν = 1 := by rw [hν]; exact mul_inv_cancel₀ hτ0
  have hxν : x = 1 + ν := by
    rw [hx, ← hτ, div_eq_mul_inv, ← hν]
    linear_combination hτν - ν * hτ
  have hmul : (!![x, x - 1, w, w; x - 1, x, w, w; u, u, 1 - x, -x; u, u, -x, 1 - x] :
      Matrix (Fin 4) (Fin 4) (ZMod p)) *
      !![x, x - 1, w, w; x - 1, x, w, w; u, u, 1 - x, -x; u, u, -x, 1 - x] = 1 := by
    rw [← hM, ← zs4h_toMatrix_mul, h.isRefl_a₄.1]; simp
  have huwτ := zs4h_fin_uw (zs4h_two_ne_zero hp) hxν hτν hmul
  rw [zs4h_fin_S4 hxν hτν huwτ] at hM
  exact zs4h_fin_sum hp h hs hτ hτν huwτ hM

private theorem zs4h_final (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F)
    {z : U ≃ₗ[ZMod p] U} (hzc : ∀ x ∈ F, z * x = x * z)
    (hz : LinearMap.toMatrix f f z.toLinearMap = -pijMat 2 3 1)
    (h₁ : orderOf (a₁ * a₄) = 2) (h₂ : orderOf (a₂ * a₄) = 3) : False := by
  have hcomm : a₁ * a₄ = a₄ * a₁ :=
    zs4h_comm_of_orderOf_two (zs4h_refl_gens h).1.1 h.isRefl_a₄.1 h₁
  obtain ⟨u, w, hM⟩ := toMatrix_refl_of_commute_pij f h.orderOf_lam h.toMatrix_a₁
    h.toMatrix_a₂ hz h.isRefl_a₄ hcomm (hzc a₄ h.a₄_mem) h₂
  exact zs4h_final_core hp h rfl rfl hM

theorem exists_basis_centre (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) :
    ∃ (c : (ZMod p)ˣ) (z : U ≃ₗ[ZMod p] U), z ∈ F ∧ (∀ x ∈ F, z * x = x * z) ∧
      FourThreeData (f.unitsSMul ![1, 1, 1, c]) lam a₁ a₂ a₃ a₄ K F ∧
      LinearMap.toMatrix (f.unitsSMul ![1, 1, 1, c]) (f.unitsSMul ![1, 1, 1, c]) z.toLinearMap =
        -pijMat 2 3 1 := by
  obtain ⟨z, hzF, -, hzc, hz, hz'⟩ := exists_centre h
  obtain ⟨b, c, hbc, hZ⟩ := zs4h_Z_anti hp h hzF hzc hz hz'
  have hb : b ≠ 0 := left_ne_zero_of_mul_eq_one hbc
  exact ⟨Units.mk0 (-b⁻¹) (by simp [hb]), z, hzF, hzc, zs4h_rescale_data h _,
    zs4h_rescale_centre hbc hb hZ⟩

theorem false (hp : p ≠ 2) (h : FourThreeData f lam a₁ a₂ a₃ a₄ K F) : False := by
  obtain ⟨a₄', -, h', h₁, h₂⟩ := exists_conj hp h
  obtain ⟨c, z, -, hzc, hf, hz⟩ := exists_basis_centre hp h'
  exact zs4h_final hp hf hzc hz h₁ h₂

end FourThreeData

end CFSG.StandardType.ZS

end
