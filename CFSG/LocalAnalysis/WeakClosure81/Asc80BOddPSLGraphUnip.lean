module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZero
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSLOuter

open Matrix

private lemma mul_smul_inv_right {k : Type*} [Field k] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} {μ : k} (hμ : μ ≠ 0) (hA2 : A * A = μ • 1) :
    A * (μ⁻¹ • A) = 1 := by
  rw [Matrix.mul_smul, hA2, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem graph_sign_normal_form {k : Type*} [Field k] {n : ℕ} {A Φ : Matrix (Fin n) (Fin n) k}
    {μ c κ : k} (hΦ : IsUnit Φ.det) (hμ : μ ≠ 0) (hA2 : A * A = μ • 1) (hΦc : Φ = c • Φᵀ)
    (hAΦ : Aᵀ * Φ * A = κ • Φ) :
    ∃ ε δ : k, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧ Φᵀ = ε • Φ ∧ Aᵀ * Φ = δ • (Φ * A) := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨1, 1, Or.inl rfl, Or.inl rfl, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · have hΦ0 : Φ ≠ 0 := by
      intro h
      apply hΦ.ne_zero
      rw [h]
      exact Matrix.det_eq_zero_of_row_eq_zero ⟨0, Nat.pos_of_ne_zero hn⟩ (by simp)
    have hΦt : Φᵀ = c • Φ := by
      simpa [Matrix.transpose_smul] using congrArg Matrix.transpose hΦc
    have hc2 : c * c = 1 := by
      have h : Φ = (c * c) • Φ := by
        calc Φ = c • Φᵀ := hΦc
          _ = c • (c • Φ) := by rw [hΦt]
          _ = (c * c) • Φ := by rw [smul_smul]
      have hzero : (c * c - 1) • Φ = 0 := by
        rw [sub_smul, ← h, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hΦ0)
    have hc : c = 1 ∨ c = -1 := sq_eq_one_iff.mp (by simpa [pow_two] using hc2)
    have hAB : A * (μ⁻¹ • A) = 1 := mul_smul_inv_right hμ hA2
    let δ : k := κ * μ⁻¹
    have hAΦ' : Aᵀ * Φ = δ • (Φ * A) := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M * (μ⁻¹ • A)) hAΦ
      simp only [Matrix.mul_assoc, hAB, Matrix.mul_one] at h
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
      simpa [δ, mul_assoc] using h
    have hAtA : Aᵀ * Aᵀ = μ • 1 := by
      have h := congrArg Matrix.transpose hA2
      simpa [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one] using h
    have hmain : μ • Φ = (δ * δ * μ) • Φ := by
      calc μ • Φ = (Aᵀ * Aᵀ) * Φ := by rw [hAtA, Matrix.smul_mul, Matrix.one_mul]
        _ = Aᵀ * (Aᵀ * Φ) := by rw [Matrix.mul_assoc]
        _ = Aᵀ * (δ • (Φ * A)) := by rw [hAΦ']
        _ = δ • (Aᵀ * (Φ * A)) := by rw [Matrix.mul_smul]
        _ = δ • ((Aᵀ * Φ) * A) := by rw [Matrix.mul_assoc]
        _ = δ • ((δ • (Φ * A)) * A) := by rw [hAΦ']
        _ = δ • (δ • ((Φ * A) * A)) := by rw [Matrix.smul_mul]
        _ = (δ * δ) • ((Φ * A) * A) := by rw [smul_smul]
        _ = (δ * δ) • (Φ * (A * A)) := by rw [Matrix.mul_assoc]
        _ = (δ * δ) • (Φ * (μ • 1)) := by rw [hA2]
        _ = (δ * δ) • (μ • (Φ * 1)) := by rw [Matrix.mul_smul]
        _ = (δ * δ) • (μ • Φ) := by rw [Matrix.mul_one]
        _ = (δ * δ * μ) • Φ := by rw [smul_smul]
    have hcoef : μ - δ * δ * μ = 0 := by
      have hzero : (μ - δ * δ * μ) • Φ = 0 := by
        rw [sub_smul, hmain, sub_self]
      exact (smul_eq_zero.mp hzero).resolve_right hΦ0
    have hδ2 : δ * δ = 1 := by
      have h1 : μ = δ * δ * μ := sub_eq_zero.mp hcoef
      have h2 : μ * 1 = μ * (δ * δ) := by
        calc μ * 1 = μ := mul_one μ
          _ = δ * δ * μ := h1
          _ = μ * (δ * δ) := mul_comm (δ * δ) μ
      exact (mul_left_cancel₀ hμ h2).symm
    have hδ : δ = 1 ∨ δ = -1 := sq_eq_one_iff.mp (by simpa [pow_two] using hδ2)
    exact ⟨c, δ, hc, hδ, hΦt, hAΦ'⟩

private lemma exists_sq_zero_commute_of_symm_neg {k : Type*} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) {n : ℕ} (hn : 3 ≤ n) {A Φ : Matrix (Fin n) (Fin n) k} {μ : k}
    (hΦ : IsUnit Φ.det) (hμ : μ ≠ 0) (hA2 : A * A = μ • 1) (hΦt : Φᵀ = Φ)
    (hAΦ : Aᵀ * Φ = -(Φ * A)) :
    ∃ N : Matrix (Fin n) (Fin n) k, N ≠ 0 ∧ N * N = 0 ∧ A * N = N * A ∧
      Nᵀ * Φ + Φ * N = 0 := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hΦu : IsUnit Φ := (Matrix.isUnit_iff_isUnit_det Φ).mpr hΦ
  let B : LinearMap.BilinForm k (Fin n → k) := Matrix.toBilin' Φ
  have hBapp : ∀ x y, B x y = x ⬝ᵥ (Φ *ᵥ y) := fun x y => Matrix.toBilin'_apply' _ _ _
  have hΦsym : Φ.IsSymm := by simpa [Matrix.IsSymm] using hΦt
  have hBsym : ∀ x y, B x y = B y x := by
    intro x y
    rw [hBapp, hBapp]
    exact Matrix.IsSymm.dotProduct_mulVec_comm hΦsym
  have hBnd : B.Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr
      (Matrix.nondegenerate_of_det_ne_zero hΦ.ne_zero)
  have hmul : ∀ x : Fin n → k, A *ᵥ (A *ᵥ x) = μ • x := by
    intro x
    rw [Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hAform : ∀ x y : Fin n → k, B (A *ᵥ x) y = - B x (A *ᵥ y) := by
    intro x y
    rw [hBapp, hBapp]
    calc (A *ᵥ x) ⬝ᵥ (Φ *ᵥ y)
        = ((A *ᵥ x) ᵥ* Φ) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
      _ = (x ᵥ* (Aᵀ * Φ)) ⬝ᵥ y := by rw [Matrix.vecMul_mulVec]
      _ = (x ᵥ* (-(Φ * A))) ⬝ᵥ y := by rw [hAΦ]
      _ = -((x ᵥ* (Φ * A)) ⬝ᵥ y) := by rw [Matrix.vecMul_neg, neg_dotProduct]
      _ = -(((x ᵥ* Φ) ᵥ* A) ⬝ᵥ y) := by rw [Matrix.vecMul_vecMul]
      _ = -((x ᵥ* Φ) ⬝ᵥ (A *ᵥ y)) := by rw [(Matrix.dotProduct_mulVec _ _ _).symm]
      _ = -(x ⬝ᵥ (Φ *ᵥ (A *ᵥ y))) := by rw [(Matrix.dotProduct_mulVec _ _ _).symm]
  have hBww : ∀ x, B (A *ᵥ x) (A *ᵥ x) = -(μ * B x x) := by
    intro x
    have h := hAform x (A *ᵥ x)
    rw [hmul x, map_smul, smul_eq_mul] at h
    exact h
  have hBvw : ∀ x, B x (A *ᵥ x) = 0 := by
    intro x
    have heq : B x (A *ᵥ x) = - B x (A *ᵥ x) := by
      calc B x (A *ᵥ x) = B (A *ᵥ x) x := (hBsym _ _).symm
        _ = - B x (A *ᵥ x) := hAform x x
    have h2eq : (2 : k) * B x (A *ᵥ x) = 0 := by
      rw [two_mul]
      nth_rewrite 2 [heq]
      abel
    exact (mul_eq_zero.mp h2eq).resolve_left h2
  obtain ⟨v0, hv0ne, hv0iso⟩ :=
    CFSG.FiniteField.exists_ne_zero_dotProduct_mulVec_eq_zero (K := k) (σ := Fin n)
      (by simpa using hn) Φ
  have hv0B : B v0 v0 = 0 := by rw [hBapp]; exact hv0iso
  have hpairdata : ∃ v w : Fin n → k, w = A *ᵥ v ∧ v ⬝ᵥ (Φ *ᵥ v) = 0 ∧
      w ⬝ᵥ (Φ *ᵥ w) = 0 ∧ v ⬝ᵥ (Φ *ᵥ w) = 0 ∧ LinearIndependent k ![v, w] := by
    by_cases hLI : LinearIndependent k ![v0, A *ᵥ v0]
    · have hwwB : B (A *ᵥ v0) (A *ᵥ v0) = 0 := by
        rw [hBww, hv0B, mul_zero, neg_zero]
      have hvwB : B v0 (A *ᵥ v0) = 0 := hBvw v0
      refine ⟨v0, A *ᵥ v0, rfl, hv0iso, ?_, ?_, hLI⟩
      · rw [← hBapp]; exact hwwB
      · rw [← hBapp]; exact hvwB
    · have hdep : ∃ c : k, A *ᵥ v0 = c • v0 := by
        have hnot : ¬ ∀ c : k, c • v0 ≠ A *ᵥ v0 := by
          intro h
          exact hLI ((LinearIndependent.pair_iff' hv0ne).mpr h)
        push Not at hnot
        obtain ⟨c, hc⟩ := hnot
        exact ⟨c, hc.symm⟩
      obtain ⟨c, hc⟩ := hdep
      have hc2 : c * c = μ := by
        have h3 : A *ᵥ (A *ᵥ v0) = (c * c) • v0 := by
          rw [hc, Matrix.mulVec_smul, hc, smul_smul]
        have h4 : A *ᵥ (A *ᵥ v0) = μ • v0 := hmul v0
        rw [h3] at h4
        have hzero : (c * c - μ) • v0 = 0 := by
          rw [sub_smul, h4, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv0ne)
      have hc0 : c ≠ 0 := by
        intro h0
        apply hμ
        rw [← hc2, h0, mul_zero]
      let W : Submodule k (Fin n → k) := LinearMap.ker ((A - c • 1).mulVecLin)
      have hWker : ∀ x, x ∈ W ↔ (A - c • 1) *ᵥ x = 0 := by
        intro x
        rw [show W = LinearMap.ker ((A - c • 1).mulVecLin) from rfl,
          LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hWmemA : ∀ x, x ∈ W ↔ A *ᵥ x = c • x := by
        intro x
        rw [hWker x, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
      have hWorth : W ≤ B.orthogonal W := by
        intro x hx
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro y hy
        have hx' : A *ᵥ x = c • x := (hWmemA x).mp hx
        have hy' : A *ᵥ y = c • y := (hWmemA y).mp hy
        have h := hAform x y
        rw [hx', hy'] at h
        have hscalar : c * B x y = -(c * B x y) := by
          simpa [map_smul, smul_eq_mul] using h
        have h2eq : (2 : k) * (c * B x y) = 0 := by
          rw [two_mul]
          nth_rewrite 2 [hscalar]
          abel
        have hcB : c * B x y = 0 := (mul_eq_zero.mp h2eq).resolve_left h2
        rw [hBsym y x]
        exact (mul_eq_zero.mp hcB).resolve_left hc0
      have hWdim : 2 * Module.finrank k W ≤ n := by
        have hle : Module.finrank k W ≤ Module.finrank k (B.orthogonal W) :=
          Submodule.finrank_mono hWorth
        have horth : Module.finrank k (B.orthogonal W) =
            Module.finrank k (Fin n → k) - Module.finrank k W :=
          LinearMap.BilinForm.finrank_orthogonal hBnd W
        rw [horth, Module.finrank_fin_fun] at hle
        have hWV : Module.finrank k W ≤ n := by
          simpa [Module.finrank_fin_fun] using Submodule.finrank_le W
        omega
      have hOdim : Module.finrank k (B.orthogonal (Submodule.span k {v0})) = n - 1 := by
        rw [LinearMap.BilinForm.finrank_orthogonal hBnd,
          finrank_span_singleton hv0ne, Module.finrank_fin_fun]
      have hnotle : ¬ B.orthogonal (Submodule.span k {v0}) ≤ W := by
        intro hle
        have h := Submodule.finrank_mono hle
        rw [hOdim] at h
        omega
      obtain ⟨y, hyOrth, hyNotW⟩ : ∃ y, y ∈ B.orthogonal (Submodule.span k {v0}) ∧ y ∉ W := by
        by_contra h
        rw [not_exists] at h
        exact hnotle fun y hy => by
          by_contra hyW
          exact h y ⟨hy, hyW⟩
      have hyOrth0 : B v0 y = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hyOrth) v0
          (Submodule.subset_span (by simp))
      let y' : Fin n → k := (A - c • 1) *ᵥ y
      have hy'0 : y' ≠ 0 := by
        intro h0
        exact hyNotW ((hWker y).mpr (by simpa [y'] using h0))
      have hy'eq : y' = A *ᵥ y - c • y := by
        simp [y', Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      have hfac : A * (A - c • 1) = -(c • (A - c • 1)) := by
        rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_sub, smul_smul,
          hA2, hc2]
        module
      have hAy' : A *ᵥ y' = -c • y' := by
        have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M *ᵥ y) hfac
        rw [← Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec] at h
        simpa [y', Matrix.neg_mulVec, Matrix.smul_mulVec] using h
      have hy'W : y' ∉ W := by
        intro hy'
        have h1 : A *ᵥ y' = c • y' := (hWmemA y').mp hy'
        have heq : c • y' = -(c • y') := by
          calc c • y' = A *ᵥ y' := h1.symm
            _ = (-c) • y' := hAy'
            _ = -(c • y') := by rw [neg_smul]
        have hzero : (2 : k) • (c • y') = 0 := by
          rw [two_smul]
          nth_rewrite 2 [heq]
          exact add_neg_cancel (c • y')
        have hcY : c • y' = 0 := (smul_eq_zero.mp hzero).resolve_left h2
        exact hy'0 ((smul_eq_zero.mp hcY).resolve_left hc0)
      have hv0Ay : B v0 (A *ᵥ y) = 0 := by
        have h := hAform v0 y
        rw [hc] at h
        have hleft : B (c • v0) y = 0 := by
          rw [map_smul, LinearMap.smul_apply, hyOrth0, smul_zero]
        rw [hleft] at h
        exact neg_eq_zero.mp h.symm
      have hy'y'B : B y' y' = 0 := by
        have h := hAform y' y'
        rw [hAy'] at h
        have heq : B (-c • y') y' = - B (-c • y') y' := by
          rw [← hBsym (-c • y') y'] at h
          exact h
        have h2eq : (2 : k) * B (-c • y') y' = 0 := by
          rw [two_mul]
          nth_rewrite 2 [heq]
          abel
        have hzero : B (-c • y') y' = 0 := (mul_eq_zero.mp h2eq).resolve_left h2
        have hlin : B (-c • y') y' = (-c) * B y' y' := by simp
        rw [hlin] at hzero
        exact (mul_eq_zero.mp hzero).resolve_left (neg_ne_zero.mpr hc0)
      have hv0y' : B v0 y' = 0 := by
        rw [hy'eq]
        simp only [map_sub, map_smul, hv0Ay, hyOrth0, smul_zero, sub_zero]
      have hv0W : v0 ∈ W := (hWmemA v0).mpr hc
      have hspanW : Submodule.span k ({v0} : Set (Fin n → k)) ≤ W := by
        rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rwa [hx]
      have hy'span : y' ∉ Submodule.span k ({v0} : Set (Fin n → k)) :=
        fun hy' => hy'W (hspanW hy')
      have hLI0 : LinearIndependent k ![v0, y'] := by
        rw [LinearIndependent.pair_iff' hv0ne]
        intro a ha
        exact hy'span (by
          rw [← ha]
          exact Submodule.smul_mem _ a (Submodule.subset_span (by simp)))
      let v : Fin n → k := v0 + y'
      have hAv : A *ᵥ v = c • v0 - c • y' := by
        rw [show v = v0 + y' from rfl, Matrix.mulVec_add, hc, hAy', sub_eq_add_neg]
        module
      have hLIv : LinearIndependent k ![v, A *ᵥ v] := by
        rw [hAv, LinearIndependent.pair_iff]
        intro s t hst
        have hdecomp : (s + t * c) • v0 + (s - t * c) • y' = 0 := by
          have h := hst
          rw [show v = v0 + y' from rfl, smul_add, smul_sub, smul_smul, smul_smul] at h
          linear_combination (norm := module) h
        obtain ⟨hcoef1, hcoef2⟩ :=
          (LinearIndependent.pair_iff.mp hLI0) (s + t * c) (s - t * c) hdecomp
        have hs2 : (2 : k) * s = 0 := by linear_combination hcoef1 + hcoef2
        have ht2 : (2 : k) * (t * c) = 0 := by linear_combination hcoef1 - hcoef2
        have hs : s = 0 := (mul_eq_zero.mp hs2).resolve_left h2
        have htc : t * c = 0 := (mul_eq_zero.mp ht2).resolve_left h2
        exact ⟨hs, (mul_eq_zero.mp htc).resolve_right hc0⟩
      have hvvB : B v v = 0 := by
        simp only [show v = v0 + y' from rfl, map_add, LinearMap.add_apply]
        rw [hBsym y' v0, hv0B, hv0y', hy'y'B]
        abel
      have hvwB : B v (A *ᵥ v) = 0 := hBvw v
      have hwwB : B (A *ᵥ v) (A *ᵥ v) = 0 := by
        rw [hBww, hvvB, mul_zero, neg_zero]
      refine ⟨v, A *ᵥ v, rfl, ?_, ?_, ?_, hLIv⟩
      · rw [← hBapp]; exact hvvB
      · rw [← hBapp]; exact hwwB
      · rw [← hBapp]; exact hvwB
  obtain ⟨v, w, hw, hvv, hww, hvw, hLI⟩ := hpairdata
  have hwv : w ⬝ᵥ (Φ *ᵥ v) = 0 := by
    rw [Matrix.IsSymm.dotProduct_mulVec_comm hΦsym]
    exact hvw
  let T : Matrix (Fin n) (Fin n) k := vecMulVec v w - vecMulVec w v
  let N : Matrix (Fin n) (Fin n) k := T * Φ
  have hTtr : Tᵀ = -T := by
    simp only [T, Matrix.transpose_sub, Matrix.transpose_vecMulVec]
    abel
  have hφwv : (w ᵥ* Φ) ⬝ᵥ v = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hwv
  have hφww : (w ᵥ* Φ) ⬝ᵥ w = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hww
  have hφvv : (v ᵥ* Φ) ⬝ᵥ v = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hvv
  have hφvw : (v ᵥ* Φ) ⬝ᵥ w = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hvw
  have hTΦT : T * Φ * T = 0 := by
    have hTΦ : T * Φ = vecMulVec v (w ᵥ* Φ) - vecMulVec w (v ᵥ* Φ) := by
      simp only [T, Matrix.sub_mul, Matrix.vecMulVec_mul]
    rw [hTΦ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
    simp [hφwv, hφww, hφvv, hφvw]
  have hNN : N * N = 0 := by
    show (T * Φ) * (T * Φ) = 0
    rw [← Matrix.mul_assoc (T * Φ) T Φ, hTΦT, Matrix.zero_mul]
  have hAT : A * T = -(T * Aᵀ) := by
    have hAw : A *ᵥ w = μ • v := by
      rw [hw, Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [T, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    rw [← hw, hAw, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
    abel
  have hAN : A * N = N * A := by
    calc A * N = A * (T * Φ) := rfl
      _ = (A * T) * Φ := by rw [Matrix.mul_assoc]
      _ = (-(T * Aᵀ)) * Φ := by rw [hAT]
      _ = -((T * Aᵀ) * Φ) := by rw [Matrix.neg_mul]
      _ = -(T * (Aᵀ * Φ)) := by rw [Matrix.mul_assoc]
      _ = -(T * (-(Φ * A))) := by rw [hAΦ]
      _ = T * (Φ * A) := by rw [Matrix.mul_neg, neg_neg]
      _ = (T * Φ) * A := by rw [Matrix.mul_assoc]
      _ = N * A := rfl
  have hNtr : Nᵀ = -(Φ * T) := by
    show (T * Φ)ᵀ = -(Φ * T)
    rw [Matrix.transpose_mul, hΦt, hTtr, Matrix.mul_neg]
  have hNadj : Nᵀ * Φ + Φ * N = 0 := by
    calc Nᵀ * Φ + Φ * N = (-(Φ * T)) * Φ + Φ * (T * Φ) := by rw [hNtr]
      _ = -((Φ * T) * Φ) + (Φ * T) * Φ := by
        rw [Matrix.neg_mul, show Φ * (T * Φ) = (Φ * T) * Φ from (Matrix.mul_assoc _ _ _).symm]
      _ = 0 := by abel
  have hT0 : T ≠ 0 := by
    intro hTzero
    have hv0 : v ≠ 0 := by simpa using hLI.ne_zero (0 : Fin 2)
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext fun j => by simpa using h j)
    have hentry : ∀ j, v i * w j = w i * v j := by
      intro j
      have h := congrFun (congrFun hTzero i) j
      simp only [T, Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.zero_apply] at h
      exact sub_eq_zero.mp h
    have hw_eq : w = (w i / v i) • v := by
      funext j
      have h := hentry j
      calc w j = (v i)⁻¹ * (v i * w j) := by
            rw [← mul_assoc, inv_mul_cancel₀ hi, one_mul]
        _ = (v i)⁻¹ * (w i * v j) := by rw [h]
        _ = (w i / v i) * v j := by rw [div_eq_inv_mul]; ring
    exact (LinearIndependent.pair_iff' hv0).mp hLI (w i / v i) hw_eq.symm
  have hN0 : N ≠ 0 := by
    intro hN
    exact hT0 ((IsUnit.mul_left_eq_zero hΦu).mp hN)
  exact ⟨N, hN0, hNN, hAN, hNadj⟩

private lemma exists_sq_zero_commute_of_alt_selfadjoint {k : Type*} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) {n : ℕ} (hn : 3 ≤ n) {A Φ : Matrix (Fin n) (Fin n) k} {μ : k}
    (hΦ : IsUnit Φ.det) (hμ : μ ≠ 0) (hA2 : A * A = μ • 1) (hΦt : Φᵀ = -Φ)
    (hAΦ : Aᵀ * Φ = Φ * A) :
    ∃ N : Matrix (Fin n) (Fin n) k, N ≠ 0 ∧ N * N = 0 ∧ A * N = N * A ∧
      Nᵀ * Φ + Φ * N = 0 := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hΦu : IsUnit Φ := (Matrix.isUnit_iff_isUnit_det Φ).mpr hΦ
  let z : Fin n → k := Pi.single ⟨0, by omega⟩ 1
  have hz0 : z ≠ 0 := by simp [z]
  have hzz_dot : z ⬝ᵥ z = 1 := by simp [z]
  let w : Fin n → k := A *ᵥ z
  have hAw : A *ᵥ w = μ • z := by
    rw [show w = A *ᵥ z from rfl, Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hanti : ∀ x y : Fin n → k, x ⬝ᵥ (Φ *ᵥ y) = -(y ⬝ᵥ (Φ *ᵥ x)) := by
    intro x y
    have h := Matrix.dotProduct_transpose_mulVec Φ y x
    rw [hΦt, Matrix.neg_mulVec, dotProduct_neg] at h
    exact h.symm
  have hself : ∀ x y : Fin n → k,
      (A *ᵥ x) ⬝ᵥ (Φ *ᵥ y) = x ⬝ᵥ (Φ *ᵥ (A *ᵥ y)) := by
    intro x y
    calc (A *ᵥ x) ⬝ᵥ (Φ *ᵥ y)
        = ((A *ᵥ x) ᵥ* Φ) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
      _ = (x ᵥ* (Aᵀ * Φ)) ⬝ᵥ y := by rw [Matrix.vecMul_mulVec]
      _ = (x ᵥ* (Φ * A)) ⬝ᵥ y := by rw [hAΦ]
      _ = (((x ᵥ* Φ) ᵥ* A)) ⬝ᵥ y := by rw [Matrix.vecMul_vecMul]
      _ = (x ᵥ* Φ) ⬝ᵥ (A *ᵥ y) := (Matrix.dotProduct_mulVec _ _ _).symm
      _ = x ⬝ᵥ (Φ *ᵥ (A *ᵥ y)) := (Matrix.dotProduct_mulVec _ _ _).symm
  have hzz : z ⬝ᵥ (Φ *ᵥ z) = 0 := by
    have heq : z ⬝ᵥ (Φ *ᵥ z) = -(z ⬝ᵥ (Φ *ᵥ z)) := hanti z z
    have h2eq : (2 : k) * (z ⬝ᵥ (Φ *ᵥ z)) = 0 := by
      rw [two_mul]
      nth_rewrite 2 [heq]
      abel
    exact (mul_eq_zero.mp h2eq).resolve_left h2
  have hww : w ⬝ᵥ (Φ *ᵥ w) = 0 := by
    have h := hself z w
    rw [hAw, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hzz, mul_zero] at h
    exact h
  have hzw : z ⬝ᵥ (Φ *ᵥ w) = 0 := by
    have h1 := hself z z
    have h2' := hanti z w
    have heq : z ⬝ᵥ (Φ *ᵥ w) = -(z ⬝ᵥ (Φ *ᵥ w)) := by
      calc z ⬝ᵥ (Φ *ᵥ w) = -(w ⬝ᵥ (Φ *ᵥ z)) := h2'
        _ = -(z ⬝ᵥ (Φ *ᵥ w)) := by rw [h1]
    have h2eq : (2 : k) * (z ⬝ᵥ (Φ *ᵥ w)) = 0 := by
      rw [two_mul]
      nth_rewrite 2 [heq]
      abel
    exact (mul_eq_zero.mp h2eq).resolve_left h2
  have hwz : w ⬝ᵥ (Φ *ᵥ z) = 0 := by
    have h := hanti z w
    rw [hzw] at h
    exact neg_eq_zero.mp h.symm
  let S : Matrix (Fin n) (Fin n) k := vecMulVec z z + μ⁻¹ • vecMulVec w w
  let N : Matrix (Fin n) (Fin n) k := S * Φ
  have hAS : A * S = S * Aᵀ := by
    have h1 : A * vecMulVec z z = vecMulVec w z := by
      rw [Matrix.mul_vecMulVec]
    have h2' : A * (μ⁻¹ • vecMulVec w w) = vecMulVec z w := by
      rw [Matrix.mul_smul, Matrix.mul_vecMulVec, hAw, Matrix.smul_vecMulVec, smul_smul,
        inv_mul_cancel₀ hμ, one_smul]
    have h3 : vecMulVec z z * Aᵀ = vecMulVec z w := by
      rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    have h4 : (μ⁻¹ • vecMulVec w w) * Aᵀ = vecMulVec w z := by
      rw [Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hAw,
        Matrix.vecMulVec_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    calc A * S = A * vecMulVec z z + A * (μ⁻¹ • vecMulVec w w) := by
          rw [show S = vecMulVec z z + μ⁻¹ • vecMulVec w w from rfl, Matrix.mul_add]
      _ = vecMulVec w z + vecMulVec z w := by rw [h1, h2']
      _ = vecMulVec z w + vecMulVec w z := by rw [add_comm]
      _ = vecMulVec z z * Aᵀ + (μ⁻¹ • vecMulVec w w) * Aᵀ := by rw [h3, h4]
      _ = S * Aᵀ := by
        rw [show S = vecMulVec z z + μ⁻¹ • vecMulVec w w from rfl, Matrix.add_mul]
  have hφzz : (z ᵥ* Φ) ⬝ᵥ z = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hzz
  have hφzw : (z ᵥ* Φ) ⬝ᵥ w = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hzw
  have hφwz : (w ᵥ* Φ) ⬝ᵥ z = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hwz
  have hφww : (w ᵥ* Φ) ⬝ᵥ w = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hww
  have hSΦS : S * Φ * S = 0 := by
    have hSΦ : S * Φ = vecMulVec z (z ᵥ* Φ) + μ⁻¹ • vecMulVec w (w ᵥ* Φ) := by
      simp only [S, Matrix.add_mul, Matrix.smul_mul, Matrix.vecMulVec_mul]
    rw [hSΦ]
    simp only [S]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
    simp [hφzz, hφzw, hφwz, hφww]
  have hNN : N * N = 0 := by
    show (S * Φ) * (S * Φ) = 0
    rw [← Matrix.mul_assoc (S * Φ) S Φ, hSΦS, Matrix.zero_mul]
  have hAN : A * N = N * A := by
    calc A * N = A * (S * Φ) := rfl
      _ = (A * S) * Φ := by rw [Matrix.mul_assoc]
      _ = (S * Aᵀ) * Φ := by rw [hAS]
      _ = S * (Aᵀ * Φ) := by rw [Matrix.mul_assoc]
      _ = S * (Φ * A) := by rw [hAΦ]
      _ = (S * Φ) * A := by rw [Matrix.mul_assoc]
      _ = N * A := rfl
  have hStr : Sᵀ = S := by
    simp only [S, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  have hNtr : Nᵀ = -(Φ * S) := by
    show (S * Φ)ᵀ = -(Φ * S)
    rw [Matrix.transpose_mul, hΦt, hStr, Matrix.neg_mul]
  have hNadj : Nᵀ * Φ + Φ * N = 0 := by
    calc Nᵀ * Φ + Φ * N = (-(Φ * S)) * Φ + Φ * (S * Φ) := by rw [hNtr]
      _ = -((Φ * S) * Φ) + (Φ * S) * Φ := by
        rw [Matrix.neg_mul, show Φ * (S * Φ) = (Φ * S) * Φ from (Matrix.mul_assoc _ _ _).symm]
      _ = 0 := by abel
  have hS0 : S ≠ 0 := by
    have hSz : S *ᵥ z = z + (μ⁻¹ * (w ⬝ᵥ z)) • w := by
      simp only [S, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hzz_dot,
        one_smul, smul_smul, op_smul_eq_smul]
    by_cases hLI : LinearIndependent k ![z, w]
    · intro hS
      have hzero : S *ᵥ z = 0 := by rw [hS, Matrix.zero_mulVec]
      rw [hSz] at hzero
      set a : k := μ⁻¹ * (w ⬝ᵥ z) with ha
      by_cases ha0 : a = 0
      · rw [ha0, zero_smul, add_zero] at hzero
        exact hz0 hzero
      · have haw : a • w = -z := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hzero
        have hw_eq : w = (-a⁻¹) • z := by
          calc w = a⁻¹ • (a • w) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
            _ = a⁻¹ • (-z) := by rw [haw]
            _ = (-a⁻¹) • z := by rw [smul_neg, neg_smul]
        exact (LinearIndependent.pair_iff' hz0).mp hLI (-a⁻¹) hw_eq.symm
    · intro hS
      have hzero : S *ᵥ z = 0 := by rw [hS, Matrix.zero_mulVec]
      rw [hSz] at hzero
      have hnot : ¬ ∀ c : k, c • z ≠ w := by
        intro h
        exact hLI ((LinearIndependent.pair_iff' hz0).mpr h)
      push Not at hnot
      obtain ⟨c, hcw⟩ := hnot
      have hc2 : c * c = μ := by
        have h1 : A *ᵥ w = μ • z := hAw
        rw [← hcw, Matrix.mulVec_smul, show A *ᵥ z = w from rfl, ← hcw, smul_smul] at h1
        have hzero' : (c * c - μ) • z = 0 := by
          rw [sub_smul, h1, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp hzero').resolve_right hz0)
      have hwz_dot : w ⬝ᵥ z = c := by
        rw [← hcw, smul_dotProduct, hzz_dot, smul_eq_mul, mul_one]
      rw [hwz_dot, ← hcw, smul_smul, mul_assoc, hc2, inv_mul_cancel₀ hμ, one_smul] at hzero
      have h2z : (2 : k) • z = 0 := by
        rw [two_smul]
        exact hzero
      exact hz0 ((smul_eq_zero.mp h2z).resolve_left h2)
  have hN0 : N ≠ 0 := by
    intro hN
    exact hS0 ((IsUnit.mul_left_eq_zero hΦu).mp hN)
  exact ⟨N, hN0, hNN, hAN, hNadj⟩

theorem exists_sq_zero_commute_isometry_of_not_orth {k : Type*} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) {n : ℕ} (hn : 3 ≤ n) {A Φ : Matrix (Fin n) (Fin n) k} {μ ε δ : k}
    (hΦ : IsUnit Φ.det) (hμ : μ ≠ 0) (hA2 : A * A = μ • 1) (hε : ε = 1 ∨ ε = -1)
    (hδ : δ = 1 ∨ δ = -1) (hΦt : Φᵀ = ε • Φ) (hAΦ : Aᵀ * Φ = δ • (Φ * A))
    (hno : ¬ (ε = 1 ∧ δ = 1)) :
    ∃ N : Matrix (Fin n) (Fin n) k, N ≠ 0 ∧ N * N = 0 ∧ A * N = N * A ∧
      Nᵀ * Φ + Φ * N = 0 := by
  classical
  have hΦu : IsUnit Φ := (Matrix.isUnit_iff_isUnit_det Φ).mpr hΦ
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
  · exact absurd ⟨rfl, rfl⟩ hno
  · have hΦt' : Φᵀ = Φ := by simpa using hΦt
    have hAΦ' : Aᵀ * Φ = -(Φ * A) := by simpa using hAΦ
    exact exists_sq_zero_commute_of_symm_neg hk hn hΦ hμ hA2 hΦt' hAΦ'
  · have hΦt' : Φᵀ = -Φ := by simpa using hΦt
    have hAΦ' : Aᵀ * Φ = Φ * A := by simpa using hAΦ
    exact exists_sq_zero_commute_of_alt_selfadjoint hk hn hΦ hμ hA2 hΦt' hAΦ'
  · have hΦt' : Φᵀ = -Φ := by simpa using hΦt
    have hAΦ' : Aᵀ * Φ = -(Φ * A) := by simpa using hAΦ
    let Φ' : Matrix (Fin n) (Fin n) k := Φ * A
    have hΦAunit : IsUnit Φ' := hΦu.mul (IsUnit.of_mul_eq_one _ (mul_smul_inv_right hμ hA2))
    have hΦ' : IsUnit Φ'.det := (Matrix.isUnit_iff_isUnit_det Φ').mp hΦAunit
    have hΦ't : Φ'ᵀ = Φ' := by
      calc Φ'ᵀ = Aᵀ * Φᵀ := by rw [show Φ' = Φ * A from rfl, Matrix.transpose_mul]
        _ = Aᵀ * (-Φ) := by rw [hΦt']
        _ = -(Aᵀ * Φ) := by rw [Matrix.mul_neg]
        _ = -(-(Φ * A)) := by rw [hAΦ']
        _ = Φ * A := by rw [neg_neg]
        _ = Φ' := rfl
    have hAΦ'' : Aᵀ * Φ' = -(Φ' * A) := by
      calc Aᵀ * Φ' = (Aᵀ * Φ) * A := by rw [show Φ' = Φ * A from rfl, Matrix.mul_assoc]
        _ = (-(Φ * A)) * A := by rw [hAΦ']
        _ = -((Φ * A) * A) := by rw [Matrix.neg_mul]
        _ = -(Φ * (A * A)) := by rw [Matrix.mul_assoc]
        _ = -(Φ * (μ • 1)) := by rw [hA2]
        _ = -(μ • (Φ * 1)) := by rw [Matrix.mul_smul]
        _ = -(μ • Φ) := by rw [Matrix.mul_one]
        _ = -(Φ' * A) := by rw [show Φ' * A = (Φ * A) * A from rfl, Matrix.mul_assoc,
          hA2, Matrix.mul_smul, Matrix.mul_one]
    obtain ⟨N, hN0, hNN, hAN, hNadj⟩ :=
      exists_sq_zero_commute_of_symm_neg hk hn hΦ' hμ hA2 hΦ't hAΦ''
    have hright : (μ⁻¹ • A) * A = 1 := by
      rw [Matrix.smul_mul, hA2, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    have hX : (Nᵀ * Φ) * A + (Φ * N) * A = 0 := by
      rw [Matrix.mul_assoc (Nᵀ) Φ A, Matrix.mul_assoc Φ N A, ← hAN,
        ← Matrix.mul_assoc Φ A N]
      exact hNadj
    have hzero : (Nᵀ * Φ + Φ * N) * (μ⁻¹ • A) = 0 := by
      rw [Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
    have hmain : Nᵀ * Φ + Φ * N = 0 := by
      calc Nᵀ * Φ + Φ * N = ((Nᵀ * Φ + Φ * N) * (μ⁻¹ • A)) * A := by
            rw [Matrix.mul_assoc, hright, Matrix.mul_one]
        _ = 0 := by rw [hzero, Matrix.zero_mul]
    exact ⟨N, hN0, hNN, hAN, hmain⟩

end CFSG.LocalAnalysis.WeakClosure81.PSLOuter
