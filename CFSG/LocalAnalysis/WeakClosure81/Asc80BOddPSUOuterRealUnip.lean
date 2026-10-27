module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private lemma map_bar_mulVec (h : UnitaryFieldData p f K) (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) :
    M.map h.bar *ᵥ (fun i => h.bar (v i)) = fun i => h.bar ((M *ᵥ v) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

private lemma N_bar_mulVec (h : UnitaryFieldData p f K) {Y : Matrix (Fin n) (Fin n) K}
    (hYr : Y.map h.bar = Y) (v : Fin n → K) :
    (Y - 1) *ᵥ (fun i => h.bar (v i)) = fun i => h.bar (((Y - 1) *ᵥ v) i) := by
  have hYbar : Y *ᵥ (fun i => h.bar (v i)) = fun i => h.bar ((Y *ᵥ v) i) := by
    conv_lhs => rw [← hYr]
    exact map_bar_mulVec h Y v
  funext i
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub, hYbar]

private lemma exists_mulVec_ne_zero {M : Matrix (Fin n) (Fin n) K} (hM : M ≠ 0) :
    ∃ v : Fin n → K, M *ᵥ v ≠ 0 := by
  by_contra! h
  apply hM
  ext i j
  have hcol : M *ᵥ Pi.single j 1 = 0 := h (Pi.single j 1)
  rw [Matrix.mulVec_single_one] at hcol
  simpa [Matrix.col_apply] using congrFun hcol i

private lemma X_mul_Y_eq {X Y : Matrix (Fin n) (Fin n) K} (hX : IsUnit X.det)
    (hXY : X * Y * X⁻¹ = Y⁻¹) : X * Y = Y⁻¹ * X := by
  have h1 : X * Y * X⁻¹ * X = Y⁻¹ * X := by rw [hXY]
  rwa [Matrix.mul_assoc, Matrix.nonsing_inv_mul (A := X) hX, Matrix.mul_one] at h1

private lemma Y_inv_commute_N {Y : Matrix (Fin n) (Fin n) K} (hYunit : IsUnit Y.det) :
    Y⁻¹ * (Y - 1) = (Y - 1) * Y⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul (A := Y) hYunit, Matrix.mul_one,
      Matrix.mul_nonsing_inv (A := Y) hYunit, Matrix.one_mul]

private lemma X_mul_N_eq {X Y : Matrix (Fin n) (Fin n) K} (hX : IsUnit X.det)
    (hYunit : IsUnit Y.det) (hXY : X * Y * X⁻¹ = Y⁻¹) :
    X * (Y - 1) = -((Y - 1) * Y⁻¹ * X) := by
  have h1 : X * (Y - 1) = Y⁻¹ * X - X := by
    rw [Matrix.mul_sub, Matrix.mul_one, X_mul_Y_eq hX hXY]
  have h2 : Y⁻¹ * X - X = (Y⁻¹ - 1) * X := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  have h3 : Y⁻¹ - 1 = -((Y - 1) * Y⁻¹) := by
    rw [Matrix.sub_mul, Matrix.mul_nonsing_inv (A := Y) hYunit, Matrix.one_mul, neg_sub]
  rw [h1, h2, h3, Matrix.neg_mul]

theorem exists_stable_isotropic_of_inverted_unipotent (h : UnitaryFieldData p f K)
    {G X Y : Matrix (Fin n) (Fin n) K} (hYr : Y.map h.bar = Y) (hY1 : Y ≠ 1)
    (hY3 : (Y - 1) ^ 3 = 0) (hYG : Yᵀ * G * Y = G) (hX : IsUnit X.det)
    (hXY : X * Y * X⁻¹ = Y⁻¹) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, gramForm h G x y = 0) ∧
      (∀ w ∈ W, X *ᵥ w ∈ W) ∧ ∀ w ∈ W, (fun i => h.bar (w i)) ∈ W := by
  let N : Matrix (Fin n) (Fin n) K := Y - 1
  let W : Submodule K (Fin n → K) :=
    LinearMap.ker N.mulVecLin ⊓ LinearMap.range N.mulVecLin
  have hN3 : N ^ 3 = 0 := by simpa [N] using hY3
  have hN0 : N ≠ 0 := by
    intro hN
    apply hY1
    exact sub_eq_zero.mp hN
  have hYunit : IsUnit Y.det := by
    have hNil : IsNilpotent N := ⟨3, hN3⟩
    have hY_eq : Y = 1 + N := by
      show Y = 1 + (Y - 1)
      rw [add_sub_cancel]
    rw [hY_eq]
    exact (Matrix.isUnit_iff_isUnit_det (1 + N)).mp (IsNilpotent.isUnit_one_add hNil)
  have hYinvN : Y⁻¹ * N = N * Y⁻¹ := by
    simpa [N] using Y_inv_commute_N hYunit
  have hXY' : X * Y = Y⁻¹ * X := X_mul_Y_eq hX hXY
  have hXN : X * N = -(N * Y⁻¹ * X) := by
    simpa [N] using X_mul_N_eq hX hYunit hXY
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  ·
    intro hW
    rw [Submodule.eq_bot_iff] at hW
    by_cases hN2 : N ^ 2 = 0
    · obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hN0
      have hw_mem : N *ᵥ v ∈ W := by
        rw [Submodule.mem_inf]
        constructor
        · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
          rw [Matrix.mulVec_mulVec, ← pow_two, hN2, Matrix.zero_mulVec]
        · rw [LinearMap.mem_range]
          exact ⟨v, by rw [Matrix.mulVecLin_apply]⟩
      exact hv (hW _ hw_mem)
    · obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hN2
      have hw_mem : N ^ 2 *ᵥ v ∈ W := by
        rw [Submodule.mem_inf]
        constructor
        · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
          rw [Matrix.mulVec_mulVec,
            show N * N ^ 2 = N ^ 3 by rw [pow_two, ← Matrix.mul_assoc, ← pow_two, ← pow_succ],
            hN3, Matrix.zero_mulVec]
        · rw [LinearMap.mem_range]
          exact ⟨N *ᵥ v, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← pow_two]⟩
      exact hv (hW _ hw_mem)
  ·
    intro x hx y hy
    rw [Submodule.mem_inf] at hx hy
    obtain ⟨hxker, _hxrange⟩ := hx
    obtain ⟨_hyker, hyrange⟩ := hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hxker
    rw [LinearMap.mem_range] at hyrange
    obtain ⟨v, hv⟩ := hyrange
    have hv' : N *ᵥ v = y := by rw [← hv, Matrix.mulVecLin_apply]
    have hxbar_ker : N *ᵥ (fun i => h.bar (x i)) = 0 := by
      have hNx : (Y - 1) *ᵥ x = 0 := by simpa [N] using hxker
      dsimp [N]
      rw [N_bar_mulVec h hYr x, hNx]
      funext i
      simp
    have hYbx : Y *ᵥ (fun i => h.bar (x i)) = fun i => h.bar (x i) := by
      have hN : (Y - 1) *ᵥ (fun i => h.bar (x i)) = 0 := hxbar_ker
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hN
      exact sub_eq_zero.mp hN
    have hrow : ((fun i => h.bar (x i)) ᵥ* G) ᵥ* Y = (fun i => h.bar (x i)) ᵥ* G := by
      have h1 : (fun i => h.bar (x i)) ᵥ* G =
          (fun i => h.bar (x i)) ᵥ* (Yᵀ * G) := by
        conv_lhs => rw [← hYbx]
        rw [Matrix.vecMul_mulVec]
      nth_rewrite 1 [h1]
      rw [Matrix.vecMul_vecMul, hYG]
    rw [gramForm_apply, ← hv']
    calc
      (fun i => h.bar (x i)) ⬝ᵥ (G *ᵥ (N *ᵥ v))
          = (fun i => h.bar (x i)) ⬝ᵥ (G *ᵥ (Y *ᵥ v - v)) := by
              dsimp [N]
              rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = (fun i => h.bar (x i)) ⬝ᵥ (G *ᵥ (Y *ᵥ v)) -
            (fun i => h.bar (x i)) ⬝ᵥ (G *ᵥ v) := by
              rw [Matrix.mulVec_sub, dotProduct_sub]
      _ = (fun i => h.bar (x i)) ⬝ᵥ ((G * Y) *ᵥ v) -
            (fun i => h.bar (x i)) ⬝ᵥ (G *ᵥ v) := by
              rw [Matrix.mulVec_mulVec]
      _ = ((fun i => h.bar (x i)) ᵥ* (G * Y)) ⬝ᵥ v -
            ((fun i => h.bar (x i)) ᵥ* G) ⬝ᵥ v := by
              rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
      _ = (((fun i => h.bar (x i)) ᵥ* G) ᵥ* Y) ⬝ᵥ v -
            ((fun i => h.bar (x i)) ᵥ* G) ⬝ᵥ v := by
              rw [← Matrix.vecMul_vecMul]
      _ = 0 := by
              rw [hrow, sub_self]
  ·
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwker, hwrange⟩ := hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hwker
    rw [LinearMap.mem_range] at hwrange
    have hX_ker : N *ᵥ (X *ᵥ w) = 0 := by
      have hYw : Y *ᵥ w = w := by
        have hNw : (Y - 1) *ᵥ w = 0 := by simpa [N] using hwker
        rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hNw
        exact sub_eq_zero.mp hNw
      have hXw : X *ᵥ w = Y⁻¹ *ᵥ (X *ᵥ w) := by
        calc
          X *ᵥ w = X *ᵥ (Y *ᵥ w) := by rw [hYw]
          _ = (X * Y) *ᵥ w := by rw [Matrix.mulVec_mulVec]
          _ = (Y⁻¹ * X) *ᵥ w := by rw [hXY']
          _ = Y⁻¹ *ᵥ (X *ᵥ w) := by rw [← Matrix.mulVec_mulVec]
      have hYXw : Y *ᵥ (X *ᵥ w) = X *ᵥ w := by
        calc
          Y *ᵥ (X *ᵥ w) = Y *ᵥ (Y⁻¹ *ᵥ (X *ᵥ w)) := by conv_lhs => rw [hXw]
          _ = (Y * Y⁻¹) *ᵥ (X *ᵥ w) := by rw [Matrix.mulVec_mulVec]
          _ = 1 *ᵥ (X *ᵥ w) := by rw [Matrix.mul_nonsing_inv (A := Y) hYunit]
          _ = X *ᵥ w := by rw [Matrix.one_mulVec]
      have hNXw : (Y - 1) *ᵥ (X *ᵥ w) = 0 := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hYXw, sub_self]
      simpa [N] using hNXw
    have hX_range : X *ᵥ w ∈ LinearMap.range N.mulVecLin := by
      rcases hwrange with ⟨v, hv⟩
      have hv' : N *ᵥ v = w := by rw [← hv, Matrix.mulVecLin_apply]
      refine ⟨-(Y⁻¹ *ᵥ (X *ᵥ v)), ?_⟩
      calc
        N.mulVecLin (-(Y⁻¹ *ᵥ (X *ᵥ v)))
            = N *ᵥ (-(Y⁻¹ *ᵥ (X *ᵥ v))) := by rw [Matrix.mulVecLin_apply]
        _ = -(N *ᵥ (Y⁻¹ *ᵥ (X *ᵥ v))) := by rw [Matrix.mulVec_neg]
        _ = -((N * Y⁻¹) *ᵥ (X *ᵥ v)) := by rw [Matrix.mulVec_mulVec]
        _ = -((N * Y⁻¹ * X) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
        _ = (-(N * Y⁻¹ * X)) *ᵥ v := by rw [← Matrix.neg_mulVec]
        _ = (X * N) *ᵥ v := by rw [← hXN]
        _ = X *ᵥ (N *ᵥ v) := by rw [← Matrix.mulVec_mulVec]
        _ = X *ᵥ w := by rw [hv']
    rw [Submodule.mem_inf]
    exact ⟨by rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply], hX_range⟩
  ·
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwker, hwrange⟩ := hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hwker
    rw [LinearMap.mem_range] at hwrange
    have hbar_ker : N *ᵥ (fun i => h.bar (w i)) = 0 := by
      have hNw : (Y - 1) *ᵥ w = 0 := by simpa [N] using hwker
      dsimp [N]
      rw [N_bar_mulVec h hYr w, hNw]
      funext i
      simp
    have hbar_range : (fun i => h.bar (w i)) ∈ LinearMap.range N.mulVecLin := by
      rcases hwrange with ⟨v, hv⟩
      have hv' : N *ᵥ v = w := by rw [← hv, Matrix.mulVecLin_apply]
      refine ⟨fun i => h.bar (v i), ?_⟩
      rw [Matrix.mulVecLin_apply]
      dsimp [N]
      rw [N_bar_mulVec h hYr v]
      exact congrArg (fun u => fun i => h.bar (u i)) hv'
    rw [Submodule.mem_inf]
    exact ⟨by rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply], hbar_range⟩

end CFSG.LocalAnalysis.WeakClosure81.UOuter
