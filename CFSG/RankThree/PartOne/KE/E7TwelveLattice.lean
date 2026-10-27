module

public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley Matrix Polynomial CFSG.RankThree.Lattice

@[expose] def e7T12W : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  wordMat .E7 [0, 1, 2, 3, 4, 5]

@[expose] def e7T12V : Fin Tag.E7.rank → ℤ := ![1, 0, 0, 0, 0, 0, 0]

@[expose] def e7T12Alpha : Fin Tag.E7.rank → ℤ := ![0, 1, 1, 2, 1, 1, 1]

@[expose] def e7T12Beta : Fin Tag.E7.rank → ℤ := ![1, 1, 1, 2, 2, 1, 1]

@[expose] def e7T12Gamma : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 2, 2, 2, 1]

@[expose] def e7T12Cols : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ := fun j =>
  if (j : ℕ) = 0 then e7T12Alpha else if (j : ℕ) = 1 then e7T12Beta
  else if (j : ℕ) = 2 then e7T12Gamma else (e7T12W ^ ((j : ℕ) - 3)) *ᵥ e7T12V

@[expose] def e7T12WList : List (List ℤ) :=
  [[0, 1, 0, 0, 0, -1, 1], [0, 0, 1, 0, 0, -1, 1], [1, 1, 0, 0, 0, -1, 1], [0, 1, 1, 0, 0, -1, 1],
   [0, 0, 0, 1, 0, -1, 1], [0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7T12VList : List ℤ := [1, 0, 0, 0, 0, 0, 0]

@[expose] def e7T12AlphaList : List ℤ := [0, 1, 1, 2, 1, 1, 1]

@[expose] def e7T12BetaList : List ℤ := [1, 1, 1, 2, 2, 1, 1]

@[expose] def e7T12GammaList : List ℤ := [1, 1, 2, 2, 2, 2, 1]

@[expose] def e7T12ColsList : List (List ℤ) :=
  [e7T12AlphaList, e7T12BetaList, e7T12GammaList] ++
    lorbit Tag.E7.rank e7T12WList e7T12VList 4

@[expose] def e7T12SigmaList : List (List ℤ) :=
  [e7T12AlphaList, vneg Tag.E7.rank e7T12AlphaList, e7T12BetaList,
    vneg Tag.E7.rank e7T12BetaList, e7T12GammaList, vneg Tag.E7.rank e7T12GammaList]

@[expose] def e7T12Rows : List KernelRow := [
  { rep := [-2, -2, -3, -4, -3, -2, -1], fc := [0, 0, -1],
    f := [0, 0, -1, -1], h := [-1, 1, 0, 0], d := 1,
    q := [-1],
    orbit := [[-2, -2, -3, -4, -3, -2, -1], [-1, -2, -3, -4, -3, -2, -1],
            [-1, -2, -2, -4, -3, -2, -1], [-1, -1, -2, -3, -3, -2, -1],
            [0, -1, -1, -2, -2, -2, -1], [0, 0, 0, -1, -1, -1, -1], [0, 0, 0, 0, -1, -1, -1],
            [0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, -1], [-1, -1, -1, -1, -1, -1, -1],
            [-1, -1, -2, -2, -1, -1, -1], [-1, -2, -2, -3, -2, -1, -1]] },
  { rep := [0, -1, -1, -2, -2, -1, -1], fc := [0, -1, 0],
    f := [1, 0, 0, 0], h := [1, 0, 0, 0], d := 1,
    q := [],
    orbit := [[0, -1, -1, -2, -2, -1, -1], [-1, -1, -1, -2, -2, -2, -1],
            [0, 0, -1, -1, -1, -1, -1], [0, -1, 0, -1, -1, -1, -1], [-1, 0, -1, -1, -1, -1, -1],
            [0, -1, -1, -1, -1, -1, -1], [-1, -1, -1, -2, -1, -1, -1],
            [-1, -1, -2, -2, -2, -1, -1], [-1, -2, -2, -3, -2, -2, -1],
            [-1, -1, -2, -3, -2, -1, -1], [-1, -2, -2, -3, -3, -2, -1],
            [-1, -1, -2, -3, -2, -2, -1]] },
  { rep := [1, 1, 1, 1, 0, 0, 0], fc := [0, 0, 0],
    f := [1, 1, 1, 0], h := [2, -1, -1, 1], d := 2,
    q := [0, 1],
    orbit := [[1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 2, 1, 0, 0], [1, 2, 2, 3, 2, 1, 0],
            [1, 1, 2, 3, 2, 1, 0], [0, 1, 1, 2, 2, 1, 0], [0, 0, 0, 1, 1, 1, 0],
            [-1, -1, -1, -1, 0, 0, 0], [-1, -1, -2, -2, -1, 0, 0], [-1, -2, -2, -3, -2, -1, 0],
            [-1, -1, -2, -3, -2, -1, 0], [0, -1, -1, -2, -2, -1, 0], [0, 0, 0, -1, -1, -1, 0]] },
  { rep := [0, 0, 0, 0, -1, -1, 0], fc := [1, 0, -1],
    f := [1, 1, 0, 0], h := [0, 0, 1, -1], d := 1,
    q := [-1],
    orbit := [[0, 0, 0, 0, -1, -1, 0], [1, 1, 1, 1, 1, 0, 0], [1, 1, 2, 2, 1, 1, 0],
            [0, 1, 1, 2, 1, 0, 0], [1, 1, 1, 2, 2, 1, 0], [0, 0, 1, 1, 1, 1, 0],
            [-1, 0, -1, 0, 0, 0, 0], [0, -1, -1, -1, 0, 0, 0], [-1, -1, -1, -2, -1, 0, 0],
            [-1, -1, -2, -2, -2, -1, 0], [0, -1, -1, -2, -1, -1, 0], [0, 0, 0, -1, -1, 0, 0]] },
  { rep := [-1, -1, -2, -2, -1, -1, 0], fc := [0, 1, -1],
    f := [0, 0, -1, -1], h := [-1, 1, 0, 0], d := 1,
    q := [-1],
    orbit := [[-1, -1, -2, -2, -1, -1, 0], [0, -1, -1, -2, -1, 0, 0], [-1, -1, -1, -2, -2, -1, 0],
            [0, 0, -1, -1, -1, -1, 0], [1, 0, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0],
            [1, 1, 1, 2, 1, 0, 0], [1, 1, 2, 2, 2, 1, 0], [0, 1, 1, 2, 1, 1, 0],
            [0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 1, 1, 0], [-1, -1, -1, -1, -1, 0, 0]] },
  { rep := [0, 0, -1, -1, -1, 0, 0], fc := [0, 0, 0],
    f := [1, 0, 0, -1], h := [1, 0, 0, 1], d := 2,
    q := [-1, 0, -1],
    orbit := [[0, 0, -1, -1, -1, 0, 0], [0, -1, 0, -1, -1, -1, 0], [0, 1, 0, 0, 0, 0, 0],
            [1, 0, 1, 1, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0], [1, 1, 1, 2, 1, 1, 0],
            [0, 0, 1, 1, 1, 0, 0], [0, 1, 0, 1, 1, 1, 0], [0, -1, 0, 0, 0, 0, 0],
            [-1, 0, -1, -1, 0, 0, 0], [0, -1, -1, -1, -1, 0, 0], [-1, -1, -1, -2, -1, -1, 0]] },
  { rep := [-1, -1, -1, -1, -1, -1, 0], fc := [1, 0, -1],
    f := [0, 0, -1, 0], h := [-1, 0, 1, 0], d := 1,
    q := [-1],
    orbit := [[-1, -1, -1, -1, -1, -1, 0], [0, 0, -1, -1, 0, 0, 0], [0, -1, 0, -1, -1, 0, 0],
            [-1, 0, -1, -1, -1, -1, 0], [1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
            [0, 1, 0, 1, 0, 0, 0], [1, 0, 1, 1, 1, 0, 0], [0, 1, 1, 1, 1, 1, 0],
            [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0]] },
  { rep := [-1, 0, -1, -1, -1, 0, 0], fc := [0, 0, 0],
    f := [0, 0, 0, -1], h := [0, 0, 0, 1], d := 1,
    q := [-1, 0, -1],
    orbit := [[-1, 0, -1, -1, -1, 0, 0], [0, -1, -1, -1, -1, -1, 0], [0, 0, 0, -1, 0, 0, 0],
            [0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, -1, 0], [1, 1, 1, 1, 1, 1, 0],
            [0, 0, 1, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0], [1, 0, 1, 1, 1, 1, 0],
            [-1, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0], [0, -1, 0, -1, 0, 0, 0]] },
  { rep := [1, 1, 2, 2, 1, 1, 1], fc := [1, 0, 0],
    f := [1, 1, 0, 0], h := [0, 0, 1, -1], d := 1,
    q := [-1],
    orbit := [[1, 1, 2, 2, 1, 1, 1], [1, 2, 2, 3, 2, 1, 1], [2, 2, 3, 4, 3, 2, 1],
            [1, 2, 3, 4, 3, 2, 1], [1, 2, 2, 4, 3, 2, 1], [1, 1, 2, 3, 3, 2, 1],
            [0, 1, 1, 2, 2, 2, 1], [0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1],
            [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1], [1, 1, 1, 1, 1, 1, 1]] },
  { rep := [0, 0, 1, 1, 1, 1, 1], fc := [1, 0, 0],
    f := [0, 0, -1, 0], h := [-1, 0, 1, 0], d := 1,
    q := [-1],
    orbit := [[0, 0, 1, 1, 1, 1, 1], [0, 1, 0, 1, 1, 1, 1], [1, 0, 1, 1, 1, 1, 1],
            [0, 1, 1, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1, 1], [1, 1, 2, 2, 2, 1, 1],
            [1, 2, 2, 3, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1], [1, 2, 2, 3, 3, 2, 1],
            [1, 1, 2, 3, 2, 2, 1], [0, 1, 1, 2, 2, 1, 1], [1, 1, 1, 2, 2, 2, 1]] }]


theorem e7T12W_eq : e7T12W = toMat Tag.E7.rank e7T12WList :=
  wordMat_eq_toMat .E7 _ (by decide +kernel)

theorem e7T12V_eq : e7T12V = toVec Tag.E7.rank e7T12VList := by decide +kernel

theorem e7T12Alpha_eq : e7T12Alpha = toVec Tag.E7.rank e7T12AlphaList := by decide +kernel

theorem e7T12Beta_eq : e7T12Beta = toVec Tag.E7.rank e7T12BetaList := by decide +kernel

theorem e7T12Gamma_eq : e7T12Gamma = toVec Tag.E7.rank e7T12GammaList := by decide +kernel

theorem e7T12Cols_eq' : e7T12Cols = fun j : Fin Tag.E7.rank => toVec Tag.E7.rank
    (e7T12ColsList.getD j []) := by
  funext j
  have hj : (j : ℕ) < 7 := j.isLt
  simp only [e7T12Cols, e7T12ColsList]
  by_cases h0 : (j : ℕ) = 0
  · rw [ite_eq_left h0, List.getD_append _ _ _ _ (by simp [e7T12AlphaList]; omega)]
    simp [h0, e7T12Alpha_eq]
  by_cases h1 : (j : ℕ) = 1
  · rw [ite_eq_right h0, ite_eq_left h1, List.getD_append _ _ _ _ (by simp [e7T12AlphaList]; omega)]
    simp [h1, e7T12Beta_eq]
  by_cases h2 : (j : ℕ) = 2
  · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2,
      List.getD_append _ _ _ _ (by simp [e7T12AlphaList]; omega)]
    simp [h2, e7T12Gamma_eq]
  · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, List.getD_append_right _ _ _ _ (by simp; omega)]
    have h3 : (j : ℕ) - ([e7T12AlphaList, e7T12BetaList, e7T12GammaList] : List (List ℤ)).length =
        (j : ℕ) - 3 := by simp
    rw [h3, toVec_lorbit_getD (by omega), e7T12W_eq, e7T12V_eq]

theorem e7T12Cols_eq :
    (Matrix.of fun i (j : Fin Tag.E7.rank) => e7T12Cols j i) =
      toMat Tag.E7.rank (lcols Tag.E7.rank e7T12ColsList) := by
  rw [← of_cols_eq_toMat, e7T12Cols_eq']

theorem e7T12Cols_det :
    (Matrix.of fun i (j : Fin Tag.E7.rank) => e7T12Cols j i).det = -1 := by
  rw [e7T12Cols_eq, det_toMat_eq]
  decide +kernel

theorem e7T12Cols_basis :
    LinearIndependent ℤ e7T12Cols ∧ Submodule.span ℤ (Set.range e7T12Cols) = ⊤ := by
  refine (Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E7.rank))).2 ?_
  rw [Module.Basis.det_apply]
  have h : (Pi.basisFun ℤ (Fin Tag.E7.rank)).toMatrix e7T12Cols =
      Matrix.of fun i (j : Fin Tag.E7.rank) => e7T12Cols j i := rfl
  rw [h, e7T12Cols_det]
  exact isUnit_one.neg

theorem e7T12W_cycle :
    e7T12W *ᵥ e7T12Alpha = e7T12Beta ∧ e7T12W *ᵥ e7T12Beta = e7T12Gamma ∧
      e7T12W *ᵥ e7T12Gamma = e7T12Alpha := by
  rw [e7T12W_eq, e7T12Alpha_eq, e7T12Beta_eq, e7T12Gamma_eq, ← toVec_lmulVec, ← toVec_lmulVec,
    ← toVec_lmulVec]
  refine ⟨congrArg _ ?_, congrArg _ ?_, congrArg _ ?_⟩ <;> decide +kernel

theorem e7T12W_pow_three_alpha : (e7T12W ^ 3) *ᵥ e7T12Alpha = e7T12Alpha := by
  rw [e7T12W_eq, e7T12Alpha_eq, ← toMat_lpow, ← toVec_lmulVec]
  exact congrArg _ (by decide +kernel)

theorem e7T12_relation :
    (e7T12W ^ 4) *ᵥ e7T12V - (e7T12W ^ 2) *ᵥ e7T12V + e7T12V = e7T12Gamma - e7T12Alpha := by
  rw [e7T12W_eq, e7T12V_eq, e7T12Gamma_eq, e7T12Alpha_eq, ← toMat_lpow, ← toMat_lpow,
    ← toVec_lmulVec, ← toVec_lmulVec]
  decide +kernel

theorem e7T12_root_kernel (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (u : ZMod p) (hu : orderOf u = 12)
    (z : Fin Tag.E7.rank → ZMod p) (hz0 : z ≠ 0)
    (hz : (e7T12W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = u • z) :
    {r | IsRoot .E7 r ∧ pair r z = 0} =
      {e7T12Alpha, -e7T12Alpha, e7T12Beta, -e7T12Beta, e7T12Gamma, -e7T12Gamma} := by
  rw [e7T12W_eq] at hz
  have hu12 : u ^ 12 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hne : ∀ k : ℕ, ¬ 12 ∣ k → u ^ k ≠ 1 := fun k hk h1 => by
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at this
    exact hk this
  have h6 : u ^ 6 + 1 = 0 := by
    have h1 : (u ^ 6 - 1) * (u ^ 6 + 1) = 0 := by linear_combination hu12
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) (hne 6 (by norm_num))
    · exact h
  have hΦu : u ^ 4 - u ^ 2 + 1 = 0 := by
    have h1 : (u ^ 2 + 1) * (u ^ 4 - u ^ 2 + 1) = 0 := by linear_combination h6
    rcases mul_eq_zero.1 h1 with h | h
    · exfalso
      have h4 : u ^ 4 = 1 := by linear_combination (u ^ 2 - 1) * h
      exact hne 4 (by norm_num) h4
    · exact h
  have hΦ : peval [1, 0, -1, 0, 1] u = 0 := by
    have h : peval [1, 0, -1, 0, 1] u = u ^ 4 - u ^ 2 + 1 := by
      simp only [peval_cons, peval_nil, Int.cast_one, Int.cast_zero, Int.cast_neg]
      ring
    rw [h, hΦu]
  have hu0 : u ≠ 0 := by
    rintro rfl
    norm_num at hu12
  have hα : pair (toVec Tag.E7.rank e7T12AlphaList) z = 0 := by
    have h := pair_pow_mulVec hz 3 (toVec Tag.E7.rank e7T12AlphaList)
    have hfix : (toMat Tag.E7.rank e7T12WList ^ 3) *ᵥ toVec Tag.E7.rank e7T12AlphaList =
        toVec Tag.E7.rank e7T12AlphaList := by
      rw [← toMat_lpow, ← toVec_lmulVec]
      exact congrArg _ (by decide +kernel)
    rw [hfix] at h
    have h2 : (1 - u ^ 3) * pair (toVec Tag.E7.rank e7T12AlphaList) z = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hne 3 (by norm_num)).symm)
  have hβ : pair (toVec Tag.E7.rank e7T12BetaList) z = 0 := by
    have h : toVec Tag.E7.rank e7T12BetaList =
        (toMat Tag.E7.rank e7T12WList) *ᵥ toVec Tag.E7.rank e7T12AlphaList := by
      rw [← toVec_lmulVec]
      decide +kernel
    rw [h, pair_mulVec hz, hα, mul_zero]
  have hγ : pair (toVec Tag.E7.rank e7T12GammaList) z = 0 := by
    have h : toVec Tag.E7.rank e7T12GammaList =
        (toMat Tag.E7.rank e7T12WList) *ᵥ toVec Tag.E7.rank e7T12BetaList := by
      rw [← toVec_lmulVec]
      decide +kernel
    rw [h, pair_mulVec hz, hβ, mul_zero]
  have hv : pair (toVec Tag.E7.rank e7T12VList) z ≠ 0 := by
    intro h0
    apply hz0
    refine eq_zero_of_pair_cols_eq_zero (B := toMat Tag.E7.rank (lcols Tag.E7.rank e7T12ColsList))
      (by rw [← e7T12Cols_eq, e7T12Cols_det]; exact isUnit_one.neg) fun j => ?_
    have hcol : (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7T12ColsList) i j) =
        toVec Tag.E7.rank (e7T12ColsList.getD j []) := by
      rw [← e7T12Cols_eq]
      exact congrFun e7T12Cols_eq' j ▸ rfl
    rw [hcol]
    have hj : (j : ℕ) < 7 := j.isLt
    by_cases h3 : (j : ℕ) < 3
    · simp only [e7T12ColsList]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 by omega) with h | h | h
      · simp [h, hα]
      · simp [h, hβ]
      · simp [h, hγ]
    · simp only [e7T12ColsList]
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      have h4 : (j : ℕ) - ([e7T12AlphaList, e7T12BetaList, e7T12GammaList] : List (List ℤ)).length =
          (j : ℕ) - 3 := by simp
      rw [h4, toVec_lorbit_getD (by omega), pair_pow_mulVec hz, h0, mul_zero]
  have hd : ∀ r ∈ e7T12Rows, r.d = 1 ∨ r.d = 2 := by decide +kernel
  have hd' : ∀ r ∈ e7T12Rows, (r.d : ZMod p) ≠ 0 := by
    intro r hr
    have h2 : (2 : ℤ) < p := by
      have := (Fact.out : p.Prime).two_le
      have : p ≠ 2 := hp2
      omega
    rcases hd r hr with h | h <;> rw [h]
    · exact intCast_zmod_ne_zero (by norm_num) (by omega)
    · exact intCast_zmod_ne_zero (by norm_num) h2
  have hker := rootKernel_eq_of_rows (τ := .E7)
    (F := [e7T12AlphaList, e7T12BetaList, e7T12GammaList]) (β := e7T12VList)
    (Φ := [1, 0, -1, 0, 1]) (m := 12) (signed := false) e7T12Rows e7T12SigmaList
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hz hu0 hΦ
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hα, hβ, hγ]) hv hd'
    (by
      intro l hl
      simp only [e7T12SigmaList, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hα
      · rw [toVec_vneg, pair_neg, hα]
        exact neg_zero
      · exact hβ
      · rw [toVec_vneg, pair_neg, hβ]
        exact neg_zero
      · exact hγ
      · rw [toVec_vneg, pair_neg, hγ]
        exact neg_zero)
  refine hker.trans ?_
  ext r
  simp only [e7T12SigmaList, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Set.mem_insert_iff, Set.mem_singleton_iff, toVec_vneg,
    ← e7T12Alpha_eq, ← e7T12Beta_eq, ← e7T12Gamma_eq]
