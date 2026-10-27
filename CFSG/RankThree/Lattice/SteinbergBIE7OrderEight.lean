module

public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial

@[expose] def e7O8W : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ := wordMat .E7 [0, 1, 2, 3, 4]

@[expose] def e7O8V : Fin Tag.E7.rank → ℤ := ![0, 0, 0, 0, 0, 1, 0]

@[expose] def e7O8Alpha : Fin Tag.E7.rank → ℤ := ![0, 0, 0, 0, 0, 0, 1]

@[expose] def e7O8Beta : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 3, 2, 2, 1]

@[expose] def e7O8Gamma : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 3, 3, 2, 1]

@[expose] def e7O8Cols : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  fun j => if (j : ℕ) < 6 then (e7O8W ^ (j : ℕ)) *ᵥ e7O8V else e7O8Alpha

@[expose] def e7O8ABG : Fin 3 → Fin Tag.E7.rank → ℤ := ![e7O8Alpha, e7O8Beta, e7O8Gamma]

@[expose] def e7O8Ext : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![e7O8Alpha, e7O8Beta, e7O8Gamma, ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0]]

@[expose] def e7O8VList : List ℤ := [0, 0, 0, 0, 0, 1, 0]

@[expose] def e7O8AlphaList : List ℤ := [0, 0, 0, 0, 0, 0, 1]

@[expose] def e7O8BetaList : List ℤ := [1, 1, 2, 3, 2, 2, 1]

@[expose] def e7O8GammaList : List ℤ := [1, 2, 2, 3, 3, 2, 1]

@[expose] def e7O8ExtList : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, 1], [1, 1, 2, 3, 2, 2, 1], [1, 2, 2, 3, 3, 2, 1], [0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0]]

@[expose] def e7O8WList : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1, 0], [0, 0, 1, 0, -1, 1, 0], [1, 1, 0, 0, -1, 1, 0], [0, 1, 1, 0, -1, 1, 0],
   [0, 0, 0, 1, -1, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7O8BasisInv : List (List ℤ) :=
  [[0, 0, -1, 1, -1, 1, 0], [1, 0, 0, -1, 1, 0, 0], [-1, 0, 2, -1, 0, 0, 0],
   [0, 1, -1, 1, -1, 0, 0], [1, -1, -1, 1, 0, 0, 0], [-1, 0, 1, -1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7O8BasisOps : List (ℕ × ℕ × ℤ) :=
  [(1, 0, 1), (0, 1, -1), (1, 0, 1), (0, 2, -1), (0, 3, -1), (0, 4, -1), (3, 1, 1), (1, 3, -1),
   (3, 1, 1), (1, 5, -1), (2, 4, -1), (4, 3, 1), (3, 4, -1), (4, 3, 1), (5, 4, 1), (4, 5, -1),
   (5, 4, 1)]

@[expose] def e7O8ExtInv : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0, 1], [2, -1, 0, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 0],
   [-3, 0, 0, 1, 0, 0, 0], [-1, -1, 0, 0, 1, 0, 0], [-2, 0, 0, 0, 0, 1, 0]]

@[expose] def e7O8Rows : List KernelRow := [
  { rep := [-2, -2, -3, -4, -3, -2, -1], fc := [-1],
    f := [0, -1, 0, 0, -1, 0], h := [1, 1, 1, 1], d := 2,
    q := [-2, -1, -1, -1],
    orbit := [[-2, -2, -3, -4, -3, -2, -1], [-1, -2, -3, -4, -3, -2, -1],
       [-1, -2, -2, -4, -3, -2, -1], [-1, -1, -2, -3, -3, -2, -1], [0, -1, -1, -2, -2, -2, -1],
       [-1, -1, -1, -2, -2, -2, -1], [-1, -1, -2, -2, -2, -2, -1], [-1, -2, -2, -3, -2, -2, -1]] },
  { rep := [-1, -2, -2, -3, -2, -1, -1], fc := [-1],
    f := [0, 0, 0, -1, 0, 0], h := [0, 1, 0, 0], d := 1,
    q := [-1],
    orbit := [[-1, -2, -2, -3, -2, -1, -1], [-1, -1, -2, -3, -2, -1, -1],
       [0, -1, -1, -2, -2, -1, -1], [0, 0, 0, -1, -1, -1, -1], [0, 0, 0, 0, -1, -1, -1],
       [0, 0, 0, 0, 0, -1, -1], [-1, -1, -1, -1, -1, -1, -1], [-1, -1, -2, -2, -1, -1, -1]] },
  { rep := [-1, -2, -2, -3, -2, -1, 0], fc := [0],
    f := [0, 0, 0, -1, 0, 0], h := [0, 1, 0, 0], d := 1,
    q := [-1],
    orbit := [[-1, -2, -2, -3, -2, -1, 0], [-1, -1, -2, -3, -2, -1, 0], [0, -1, -1, -2, -2, -1, 0],
       [0, 0, 0, -1, -1, -1, 0], [0, 0, 0, 0, -1, -1, 0], [0, 0, 0, 0, 0, -1, 0],
       [-1, -1, -1, -1, -1, -1, 0], [-1, -1, -2, -2, -1, -1, 0]] },
  { rep := [-1, -1, -2, -2, -2, -1, -1], fc := [-1],
    f := [1, -1, -1, 1, 0, -1], h := [1, 1, 1, 0], d := 1,
    q := [0, 0, -1, -1],
    orbit := [[-1, -1, -2, -2, -2, -1, -1], [0, -1, -1, -2, -1, -1, -1],
       [-1, -1, -1, -2, -2, -1, -1], [0, 0, -1, -1, -1, -1, -1], [0, -1, 0, -1, -1, -1, -1],
       [-1, 0, -1, -1, -1, -1, -1], [0, -1, -1, -1, -1, -1, -1], [-1, -1, -1, -2, -1, -1, -1]] },
  { rep := [-1, -1, -2, -2, -2, -1, 0], fc := [0],
    f := [1, -1, -1, 1, 0, -1], h := [1, 1, 1, 0], d := 1,
    q := [0, 0, -1, -1],
    orbit := [[-1, -1, -2, -2, -2, -1, 0], [0, -1, -1, -2, -1, -1, 0], [-1, -1, -1, -2, -2, -1, 0],
       [0, 0, -1, -1, -1, -1, 0], [0, -1, 0, -1, -1, -1, 0], [-1, 0, -1, -1, -1, -1, 0],
       [0, -1, -1, -1, -1, -1, 0], [-1, -1, -1, -2, -1, -1, 0]] },
  { rep := [-1, -1, -2, -2, -1, 0, 0], fc := [0],
    f := [1, 0, -1, 0, 0, 0], h := [1, 0, 1, 0], d := 2,
    q := [-1],
    orbit := [[-1, -1, -2, -2, -1, 0, 0], [0, -1, -1, -2, -1, 0, 0], [0, 0, 0, -1, -1, 0, 0],
       [1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 2, 1, 0, 0], [0, 1, 1, 2, 1, 0, 0], [0, 0, 0, 1, 1, 0, 0],
       [-1, -1, -1, -1, 0, 0, 0]] },
  { rep := [-1, -1, -1, -2, -1, 0, 0], fc := [0],
    f := [0, 0, 1, -1, -1, 1], h := [1, 1, 0, 0], d := 2,
    q := [-2, 0, 1],
    orbit := [[-1, -1, -1, -2, -1, 0, 0], [0, 0, -1, -1, -1, 0, 0], [1, 0, 1, 0, 0, 0, 0],
       [0, 1, 1, 1, 0, 0, 0], [1, 1, 1, 2, 1, 0, 0], [0, 0, 1, 1, 1, 0, 0], [-1, 0, -1, 0, 0, 0, 0],
       [0, -1, -1, -1, 0, 0, 0]] },
  { rep := [-1, -1, -1, -1, -1, 0, 0], fc := [0],
    f := [1, -1, 0, 0, 0, 0], h := [1, 1, 1, 1], d := 2,
    q := [-1],
    orbit := [[-1, -1, -1, -1, -1, 0, 0], [0, 0, -1, -1, 0, 0, 0], [0, -1, 0, -1, -1, 0, 0],
       [0, 1, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0],
       [0, 0, 0, 0, 1, 0, 0]] },
  { rep := [-1, 0, -1, -1, -1, 0, 0], fc := [0],
    f := [1, -1, 0, 1, -1, 0], h := [2, 1, 0, -1], d := 2,
    q := [0, -1, -1, 1],
    orbit := [[-1, 0, -1, -1, -1, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
       [0, 1, 0, 1, 0, 0, 0], [1, 0, 1, 1, 1, 0, 0], [-1, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0],
       [0, -1, 0, -1, 0, 0, 0]] },
  { rep := [-1, 0, -1, -1, 0, 0, 0], fc := [0],
    f := [0, 0, 0, 0, -1, 1], h := [1, 1, 1, 1], d := 2,
    q := [-2, 0, 0, 0, 1],
    orbit := [[-1, 0, -1, -1, 0, 0, 0], [0, -1, -1, -1, -1, 0, 0], [0, 0, 0, -1, 0, 0, 0],
       [0, 0, 0, 0, -1, 0, 0], [1, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0],
       [0, -1, 0, 0, 0, 0, 0]] },
  { rep := [0, 0, 0, 0, 0, 1, 0], fc := [0],
    f := [1, 0, 0, 0, 0, 0], h := [1, 0, 0, 0], d := 1,
    q := [],
    orbit := [[0, 0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 1, 0], [1, 1, 2, 2, 1, 1, 0],
       [1, 2, 2, 3, 2, 1, 0], [1, 1, 2, 3, 2, 1, 0], [0, 1, 1, 2, 2, 1, 0], [0, 0, 0, 1, 1, 1, 0],
       [0, 0, 0, 0, 1, 1, 0]] },
  { rep := [0, 0, 0, 0, 0, 1, 1], fc := [1],
    f := [1, 0, 0, 0, 0, 0], h := [1, 0, 0, 0], d := 1,
    q := [],
    orbit := [[0, 0, 0, 0, 0, 1, 1], [1, 1, 1, 1, 1, 1, 1], [1, 1, 2, 2, 1, 1, 1],
       [1, 2, 2, 3, 2, 1, 1], [1, 1, 2, 3, 2, 1, 1], [0, 1, 1, 2, 2, 1, 1], [0, 0, 0, 1, 1, 1, 1],
       [0, 0, 0, 0, 1, 1, 1]] },
  { rep := [0, 0, 1, 1, 1, 1, 0], fc := [0],
    f := [0, 0, 1, -1, 0, 1], h := [0, 1, 1, 1], d := 1,
    q := [-1, 0, 0, 1, 1],
    orbit := [[0, 0, 1, 1, 1, 1, 0], [0, 1, 0, 1, 1, 1, 0], [1, 0, 1, 1, 1, 1, 0],
       [0, 1, 1, 1, 1, 1, 0], [1, 1, 1, 2, 1, 1, 0], [1, 1, 2, 2, 2, 1, 0], [0, 1, 1, 2, 1, 1, 0],
       [1, 1, 1, 2, 2, 1, 0]] },
  { rep := [0, 0, 1, 1, 1, 1, 1], fc := [1],
    f := [0, 0, 1, -1, 0, 1], h := [0, 1, 1, 1], d := 1,
    q := [-1, 0, 0, 1, 1],
    orbit := [[0, 0, 1, 1, 1, 1, 1], [0, 1, 0, 1, 1, 1, 1], [1, 0, 1, 1, 1, 1, 1],
       [0, 1, 1, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1, 1], [1, 1, 2, 2, 2, 1, 1], [0, 1, 1, 2, 1, 1, 1],
       [1, 1, 1, 2, 2, 1, 1]] },
  { rep := [0, 1, 1, 2, 2, 2, 1], fc := [1],
    f := [1, 0, 0, 0, 0, 1], h := [1, 1, 1, 1], d := 2,
    q := [-1, 1, 1, 1, 1],
    orbit := [[0, 1, 1, 2, 2, 2, 1], [1, 1, 1, 2, 2, 2, 1], [1, 1, 2, 2, 2, 2, 1],
       [1, 2, 2, 3, 2, 2, 1], [2, 2, 3, 4, 3, 2, 1], [1, 2, 3, 4, 3, 2, 1], [1, 2, 2, 4, 3, 2, 1],
       [1, 1, 2, 3, 3, 2, 1]] }]

@[expose] def e7O8SigmaList : List (List ℤ) :=
  [e7O8AlphaList, vneg Tag.E7.rank e7O8AlphaList, e7O8BetaList, vneg Tag.E7.rank e7O8BetaList,
    e7O8GammaList, vneg Tag.E7.rank e7O8GammaList]

@[expose] def e7O8Basis : List (List ℤ) :=
  lcols Tag.E7.rank (lorbit Tag.E7.rank e7O8WList e7O8VList 6 ++ [e7O8AlphaList])

@[expose] def e7O8Conj : List (List ℤ) :=
  lmul Tag.E7.rank (lmul Tag.E7.rank e7O8BasisInv e7O8WList) e7O8Basis

@[expose] def e7O8Reps : Fin 15 → Fin Tag.E7.rank → ℤ :=
  fun k => toVec Tag.E7.rank ((e7O8Rows.map KernelRow.rep).getD k [])

theorem e7O8W_eq : e7O8W = toMat Tag.E7.rank e7O8WList :=
  wordMat_eq_toMat .E7 _ (by decide +kernel)

theorem e7O8V_eq : e7O8V = toVec Tag.E7.rank e7O8VList := by decide +kernel

theorem e7O8Alpha_eq : e7O8Alpha = toVec Tag.E7.rank e7O8AlphaList := by decide +kernel

theorem e7O8Beta_eq : e7O8Beta = toVec Tag.E7.rank e7O8BetaList := by decide +kernel

theorem e7O8Gamma_eq : e7O8Gamma = toVec Tag.E7.rank e7O8GammaList := by decide +kernel

theorem e7O8Cols_eq' : e7O8Cols = fun j : Fin Tag.E7.rank => toVec Tag.E7.rank
    ((lorbit Tag.E7.rank e7O8WList e7O8VList 6 ++ [e7O8AlphaList]).getD j []) := by
  funext j
  have hj : (j : ℕ) < 7 := j.isLt
  simp only [e7O8Cols]
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simp [lorbit]; omega), toVec_lorbit_getD h, e7O8W_eq,
      e7O8V_eq]
  · rw [List.getD_append_right _ _ _ _ (by simp [lorbit]; omega)]
    have h6 : (j : ℕ) - (lorbit Tag.E7.rank e7O8WList e7O8VList 6).length = 0 := by
      simp [lorbit]
      omega
    rw [h6, e7O8Alpha_eq]
    rfl

theorem e7O8Cols_eq :
    (Matrix.of fun i (j : Fin Tag.E7.rank) => e7O8Cols j i) = toMat Tag.E7.rank e7O8Basis := by
  rw [e7O8Basis, ← of_cols_eq_toMat, e7O8Cols_eq']

theorem e7O8_det_basis : (toMat Tag.E7.rank e7O8Basis).det = 1 := by
  rw [det_toMat_eq_of_colAdds _ e7O8BasisOps (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem e7O8Basis_mul_inv : lmul Tag.E7.rank e7O8Basis e7O8BasisInv = lid Tag.E7.rank := by
  decide +kernel

theorem e7O8Conj_blocks :
    lowerLeftZero 6 1 e7O8Conj = true ∧
      ltopLeft 6 e7O8Conj = [[0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, -1],
        [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0]] ∧
      lbotRight 6 1 e7O8Conj = [[1]] := by
  decide +kernel

theorem charpoly_e7O8W : e7O8W.charpoly = (X - 1) ^ 2 * (X + 1) * (X ^ 4 + 1) := by
  have hc : (toMat Tag.E7.rank e7O8WList).charpoly = (toMat Tag.E7.rank e7O8Conj).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E7.rank e7O8Basis)
      (B' := toMat Tag.E7.rank e7O8BasisInv)
      (by rw [← toMat_lmul, e7O8Basis_mul_inv, toMat_lid]), e7O8Conj, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e7O8Conj_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 6) (m := 1) e7O8Conj h₁
  rw [h₂, h₃, charpoly_toMat_one_by_one, map_one] at hb
  have h6 : (toMat 6 [[0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, -1],
      [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0]]).charpoly =
        X ^ 6 - X ^ 4 + X ^ 2 - 1 :=
    charpoly_eq_of_lists (cs := [-1, 0, 1, 0, -1, 0, 1]) (by monicity!) (by compute_degree!)
      (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0]
      (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 6) (by decide +kernel))
  rw [h6] at hb
  rw [e7O8W_eq, hc]
  refine Eq.trans (hb : (toMat Tag.E7.rank e7O8Conj).charpoly = _) ?_
  ring

theorem e7O8_root_kernel (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (u : ZMod p) (hu : orderOf u = 8)
    (z : Fin Tag.E7.rank → ZMod p) (hz0 : z ≠ 0)
    (hz : (e7O8W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = u • z) :
    {r | IsRoot .E7 r ∧ pair r z = 0} =
      {e7O8Alpha, -e7O8Alpha, e7O8Beta, -e7O8Beta, e7O8Gamma, -e7O8Gamma} := by
  rw [e7O8W_eq] at hz
  have hu8 : u ^ 8 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have h41 : u ^ 4 + 1 = 0 := by
    have h1 : (u ^ 4 - 1) * (u ^ 4 + 1) = 0 := by linear_combination hu8
    rcases mul_eq_zero.1 h1 with h | h
    · exfalso
      have := orderOf_dvd_of_pow_eq_one (sub_eq_zero.1 h)
      rw [hu] at this
      norm_num at this
    · exact h
  have hΦ : peval [1, 0, 0, 0, 1] u = 0 := by
    have h : peval [1, 0, 0, 0, 1] u = u ^ 4 + 1 := by
      simp only [peval_cons, peval_nil, Int.cast_one, Int.cast_zero]
      ring
    rw [h, h41]
  have hu0 : u ≠ 0 := by
    rintro rfl
    norm_num at hu8
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    norm_num at hu
  have hα : pair (toVec Tag.E7.rank e7O8AlphaList) z = 0 :=
    pair_eq_zero_of_fixed hz hu1 (by rw [← toVec_lmulVec]; exact congrArg _ (by decide +kernel))
  have hv : pair (toVec Tag.E7.rank e7O8VList) z ≠ 0 := by
    intro h0
    apply hz0
    refine eq_zero_of_pair_cols_eq_zero (B := toMat Tag.E7.rank e7O8Basis)
      (by rw [e7O8_det_basis]; exact isUnit_one) fun j => ?_
    have hcol : (fun i => toMat Tag.E7.rank e7O8Basis i j) = toVec Tag.E7.rank
        ((lorbit Tag.E7.rank e7O8WList e7O8VList 6 ++ [e7O8AlphaList]).getD j []) := by
      rw [← e7O8Cols_eq]
      exact congrFun e7O8Cols_eq' j
    rw [hcol]
    have hj : (j : ℕ) < 7 := j.isLt
    by_cases h : (j : ℕ) < 6
    · rw [List.getD_append _ _ _ _ (by simp [lorbit]; omega), toVec_lorbit_getD h,
        pair_pow_mulVec hz, h0, mul_zero]
    · rw [List.getD_append_right _ _ _ _ (by simp [lorbit]; omega)]
      have h6 : (j : ℕ) - (lorbit Tag.E7.rank e7O8WList e7O8VList 6).length = 0 := by
        simp [lorbit]
        omega
      rw [h6]
      exact hα
  have hβ : pair (toVec Tag.E7.rank e7O8BetaList) z = 0 := by
    have h : toVec Tag.E7.rank e7O8BetaList = toVec Tag.E7.rank e7O8VList +
        (toMat Tag.E7.rank e7O8WList ^ 4) *ᵥ toVec Tag.E7.rank e7O8VList +
          toVec Tag.E7.rank e7O8AlphaList := by
      rw [← toMat_lpow, ← toVec_lmulVec]
      decide +kernel
    rw [h, pair_add, pair_add, pair_pow_mulVec hz, hα, add_zero]
    calc pair (toVec Tag.E7.rank e7O8VList) z + u ^ 4 * pair (toVec Tag.E7.rank e7O8VList) z
        = (u ^ 4 + 1) * pair (toVec Tag.E7.rank e7O8VList) z := by ring
      _ = 0 := by rw [h41, zero_mul]
  have hγ : pair (toVec Tag.E7.rank e7O8GammaList) z = 0 := by
    have h : toVec Tag.E7.rank e7O8GammaList =
        (toMat Tag.E7.rank e7O8WList ^ 1) *ᵥ toVec Tag.E7.rank e7O8VList +
        (toMat Tag.E7.rank e7O8WList ^ 5) *ᵥ toVec Tag.E7.rank e7O8VList +
          toVec Tag.E7.rank e7O8AlphaList := by
      rw [← toMat_lpow, ← toMat_lpow, ← toVec_lmulVec, ← toVec_lmulVec]
      decide +kernel
    rw [h, pair_add, pair_add, pair_pow_mulVec hz, pair_pow_mulVec hz, hα, add_zero]
    calc u ^ 1 * pair (toVec Tag.E7.rank e7O8VList) z +
          u ^ 5 * pair (toVec Tag.E7.rank e7O8VList) z
        = u * (u ^ 4 + 1) * pair (toVec Tag.E7.rank e7O8VList) z := by ring
      _ = 0 := by rw [h41, mul_zero, zero_mul]
  have hd : ∀ r ∈ e7O8Rows, r.d = 1 ∨ r.d = 2 := by decide +kernel
  have hd' : ∀ r ∈ e7O8Rows, (r.d : ZMod p) ≠ 0 := by
    intro r hr
    have h2 : (2 : ℤ) < p := by
      have := (Fact.out : p.Prime).two_le
      have : p ≠ 2 := hp2
      omega
    rcases hd r hr with h | h <;> rw [h]
    · exact intCast_zmod_ne_zero (by norm_num) (by omega)
    · exact intCast_zmod_ne_zero (by norm_num) h2
  have hker := rootKernel_eq_of_rows (τ := .E7) (F := [e7O8AlphaList]) (β := e7O8VList)
    (Φ := [1, 0, 0, 0, 1]) (m := 8) (signed := false) e7O8Rows e7O8SigmaList
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hz hu0 hΦ
    (by simpa using hα) hv hd'
    (by
      intro l hl
      simp only [e7O8SigmaList, List.mem_cons, List.not_mem_nil, or_false] at hl
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
  simp only [e7O8SigmaList, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Set.mem_insert_iff, Set.mem_singleton_iff, toVec_vneg,
    ← e7O8Alpha_eq, ← e7O8Beta_eq, ← e7O8Gamma_eq]

theorem e7O8_orbits :
    (∀ k, {x | ∃ j : ℕ, x = (e7O8W ^ j) *ᵥ e7O8Reps k}.ncard = 8) ∧
    (∀ k l, k ≠ l → Disjoint {x | ∃ j : ℕ, x = (e7O8W ^ j) *ᵥ e7O8Reps k}
      {x | ∃ j : ℕ, x = (e7O8W ^ j) *ᵥ e7O8Reps l}) ∧
    {r | IsRoot .E7 r ∧ r ∉ ({e7O8Alpha, -e7O8Alpha, e7O8Beta, -e7O8Beta, e7O8Gamma,
      -e7O8Gamma} : Set (Fin Tag.E7.rank → ℤ))} =
        ⋃ k, {x | ∃ j : ℕ, x = (e7O8W ^ j) *ᵥ e7O8Reps k} ∧
    ∀ k, ∃ (c : ℤ) (f h : ℤ[X]) (d : ℤ), (d = 1 ∨ d = 2) ∧ f.natDegree < 6 ∧
      e7O8Reps k = c • e7O8Alpha + (aeval e7O8W f) *ᵥ e7O8V ∧ (X ^ 4 + 1 : ℤ[X]) ∣ f * h - C d := by
  have hw8 : toMat Tag.E7.rank e7O8WList ^ 8 = 1 := by
    rw [← toMat_lpow, ← toMat_lid]
    exact congrArg _ (by decide +kernel)
  have hrows : ∀ r ∈ e7O8Rows, r.check Tag.E7.rank e7O8WList [e7O8AlphaList] e7O8VList
      [1, 0, 0, 0, 1] 8 false = true := by
    decide +kernel
  have hlen : e7O8Rows.length = 15 := by decide +kernel
  have hrow : ∀ k : Fin 15, e7O8Rows.getD k default ∈ e7O8Rows := fun k => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.isLt)]
    exact List.getElem_mem _
  have hrep : ∀ k : Fin 15, e7O8Reps k = toVec Tag.E7.rank (e7O8Rows.getD k default).rep := by
    intro k
    simp only [e7O8Reps]
    rw [List.getD_eq_getElem _ _ (by simp [hlen]), List.getElem_map,
      List.getD_eq_getElem _ _ (by rw [hlen]; exact k.isLt)]
  have horb : ∀ (k : Fin 15) (x : Fin Tag.E7.rank → ℤ),
      (∃ j : ℕ, x = (e7O8W ^ j) *ᵥ e7O8Reps k) ↔
        ∃ l ∈ (e7O8Rows.getD k default).orbit, x = toVec Tag.E7.rank l := by
    intro k x
    have hc := hrows _ (hrow k)
    simp only [KernelRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [hc.2, lorbitSigned, ite_eq_right (by decide), List.append_nil, hrep, e7O8W_eq,
      mem_powOrbit_iff (by norm_num) hw8]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, by rw [toVec_lmulVec, toMat_lpow]⟩
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
      exact ⟨j, List.mem_range.1 hj, by rw [toVec_lmulVec, toMat_lpow]⟩
  have hlen7 : ∀ r ∈ e7O8Rows, ∀ l ∈ r.orbit, l.length = 7 := by decide +kernel
  refine ⟨fun k => ?_, fun k l hkl => ?_, ?_, fun k => ?_⟩
  · have hc := hrows _ (hrow k)
    simp only [KernelRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [hrep, e7O8W_eq]
    refine ncard_powOrbit (by norm_num) hw8 ?_
    have hnd : ∀ r ∈ e7O8Rows, (lorbit Tag.E7.rank e7O8WList r.rep 8).Nodup := by decide +kernel
    exact hnd _ (hrow k)
  · rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_ofPred_eq] at hx hx'
    obtain ⟨a, ha, rfl⟩ := (horb k x).1 hx
    obtain ⟨b, hb, hab⟩ := (horb l _).1 hx'
    have hab' := toVec_injective_of_length (hlen7 _ (hrow k) a ha) (hlen7 _ (hrow l) b hb) hab
    subst hab'
    have hdisj : ∀ (i j : Fin 15), i ≠ j → ∀ a ∈ (e7O8Rows.getD i default).orbit,
        a ∉ (e7O8Rows.getD j default).orbit := by
      decide +kernel
    exact hdisj k l hkl a ha hb
  · ext r
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, horb]
    have hcover : ∀ l ∈ Tag.E7.artifactRoots, l ∈ e7O8SigmaList ∨ ∃ k : Fin 15,
        l ∈ (e7O8Rows.getD k default).orbit := by
      decide +kernel
    have hinroots : ∀ k : Fin 15, ∀ l ∈ (e7O8Rows.getD k default).orbit,
        l ∈ Tag.E7.artifactRoots ∧ l ∉ e7O8SigmaList := by
      decide +kernel
    have hsig : ∀ x : Fin Tag.E7.rank → ℤ, x ∈ ({e7O8Alpha, -e7O8Alpha, e7O8Beta, -e7O8Beta,
        e7O8Gamma, -e7O8Gamma} : Set (Fin Tag.E7.rank → ℤ)) ↔
          ∃ l ∈ e7O8SigmaList, x = toVec Tag.E7.rank l := by
      intro x
      simp only [e7O8SigmaList, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons,
        List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, toVec_vneg,
        ← e7O8Alpha_eq, ← e7O8Beta_eq, ← e7O8Gamma_eq]
    have hsiglen : ∀ l ∈ e7O8SigmaList, l.length = 7 := by decide +kernel
    constructor
    · rintro ⟨hr, hnot⟩
      obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hr
      rcases hcover l hl with hs | ⟨k, hk⟩
      · exact absurd ((hsig _).2 ⟨l, hs, rfl⟩) hnot
      · exact ⟨k, l, hk, rfl⟩
    · rintro ⟨k, l, hl, rfl⟩
      refine ⟨isRoot_toVec (hinroots k l hl).1, fun hs => ?_⟩
      obtain ⟨l', hl', hll'⟩ := (hsig _).1 hs
      have := toVec_injective_of_length (hlen7 _ (hrow k) l hl) (hsiglen l' hl') hll'
      subst this
      exact (hinroots k l hl).2 hl'
  · have hc := hrows _ (hrow k)
    simp only [KernelRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hrep', hcong⟩, -⟩ := hc
    set r := e7O8Rows.getD k default with hr
    have hfc : ∀ r ∈ e7O8Rows, r.fc = [r.fc.headD 0] := by decide +kernel
    have hcfc := hfc r (hrow k)
    have hdr : ∀ r ∈ e7O8Rows, (r.d = 1 ∨ r.d = 2) ∧ r.f.length ≤ 6 := by decide +kernel
    refine ⟨r.fc.headD 0, polyOfList r.f, polyOfList r.h, r.d, (hdr r (hrow k)).1,
      natDegree_polyOfList_lt _ (hdr r (hrow k)).2 (by norm_num), ?_, ?_⟩
    · have hz : (fun _ : Fin Tag.E7.rank => (0 : ℤ)) = 0 := rfl
      rw [hrep, ← hrep', toVec_vadd, toVec_lpolyVec, hcfc, vcombo, vcombo, toVec_vadd,
        toVec_vsmul, toVec_vofFn, hz, add_zero, e7O8W_eq, e7O8Alpha_eq, e7O8V_eq]
      rfl
    · have hΦ : polyOfList [1, 0, 0, 0, 1] = X ^ 4 + 1 := by simp [polyOfList]; ring
      rw [← hΦ]
      exact dvd_of_cong hcong

theorem E7_order_eight_lattice_and_exact_three_A1_prime_root_kernel :
    orderOf e7O8W = 8 ∧ e7O8W.charpoly = (X - 1) ^ 2 * (X + 1) * (X ^ 4 + 1) ∧
    (LinearIndependent ℤ e7O8Cols ∧ Submodule.span ℤ (Set.range e7O8Cols) = ⊤) ∧
    (Matrix.of fun i (j : Fin Tag.E7.rank) => e7O8Cols j i).det = 1 ∧
    ((e7O8W ^ 4 + 1) * (e7O8W ^ 2 - 1)) *ᵥ e7O8V = 0 ∧
    e7O8W *ᵥ e7O8Alpha = e7O8Alpha ∧ e7O8W *ᵥ e7O8Beta = e7O8Gamma ∧
    e7O8W *ᵥ e7O8Gamma = e7O8Beta ∧ e7O8Beta = e7O8V + (e7O8W ^ 4) *ᵥ e7O8V + e7O8Alpha ∧
    e7O8Gamma = e7O8W *ᵥ e7O8V + (e7O8W ^ 5) *ᵥ e7O8V + e7O8Alpha ∧
    (∀ i, IsRoot .E7 (e7O8ABG i)) ∧ LinearIndependent ℤ e7O8ABG ∧
    (e7O8Ext 0 = e7O8Alpha ∧ e7O8Ext 1 = e7O8Beta ∧ e7O8Ext 2 = e7O8Gamma) ∧
    (Matrix.of fun i (j : Fin Tag.E7.rank) => e7O8Ext j i).det = 1 ∧
    gramMat .E7 e7O8ABG = 2 ∧
    {c : Fin 3 → ZMod 2 | ∑ i, c i • (fun r => ((Tag.E7.cartan *ᵥ e7O8ABG i) r : ZMod 2)) = 0} =
      {0, ![1, 1, 1]} ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ u : ZMod p, orderOf u = 8 →
      ∀ z : Fin Tag.E7.rank → ZMod p, z ≠ 0 →
        (e7O8W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = u • z →
        {r | IsRoot .E7 r ∧ pair r z = 0} =
          {e7O8Alpha, -e7O8Alpha, e7O8Beta, -e7O8Beta, e7O8Gamma, -e7O8Gamma}) ∧
    ∃ reps : Fin 15 → Fin Tag.E7.rank → ℤ,
      (∀ k, {x | ∃ j : ℕ, x = (e7O8W ^ j) *ᵥ reps k}.ncard = 8) ∧
      (∀ k l, k ≠ l → Disjoint {x | ∃ j : ℕ, x = (e7O8W ^ j) *ᵥ reps k}
        {x | ∃ j : ℕ, x = (e7O8W ^ j) *ᵥ reps l}) ∧
      {r | IsRoot .E7 r ∧ r ∉ ({e7O8Alpha, -e7O8Alpha, e7O8Beta, -e7O8Beta, e7O8Gamma,
        -e7O8Gamma} : Set (Fin Tag.E7.rank → ℤ))} =
          ⋃ k, {x | ∃ j : ℕ, x = (e7O8W ^ j) *ᵥ reps k} ∧
      ∀ k, ∃ (c : ℤ) (f h : ℤ[X]) (d : ℤ), (d = 1 ∨ d = 2) ∧ f.natDegree < 6 ∧
        reps k = c • e7O8Alpha + (aeval e7O8W f) *ᵥ e7O8V ∧ (X ^ 4 + 1 : ℤ[X]) ∣ f * h - C d := by
  have hABG : e7O8ABG = fun i : Fin 3 => toVec Tag.E7.rank
      ([e7O8AlphaList, e7O8BetaList, e7O8GammaList].getD i []) := by
    decide +kernel
  have hExt : e7O8Ext = fun i : Fin Tag.E7.rank => toVec Tag.E7.rank (e7O8ExtList.getD i []) := by
    decide +kernel
  refine ⟨?_, charpoly_e7O8W, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_,
    fun p hp hp2 u hu z hz0 hz => @e7O8_root_kernel p ⟨hp⟩ hp2 u hu z hz0 hz,
    e7O8Reps, e7O8_orbits⟩
  · rw [e7O8W_eq]
    exact orderOf_toMat_eq (by norm_num) (by decide +kernel) (by decide +kernel)
  · rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E7.rank)), Module.Basis.det_apply]
    have h : (Pi.basisFun ℤ (Fin Tag.E7.rank)).toMatrix e7O8Cols =
        Matrix.of fun i (j : Fin Tag.E7.rank) => e7O8Cols j i := rfl
    rw [h, e7O8Cols_eq, e7O8_det_basis]
    exact isUnit_one
  · rw [e7O8Cols_eq, e7O8_det_basis]
  · have h : (e7O8W ^ 4 + 1) * (e7O8W ^ 2 - 1) = toMat Tag.E7.rank (lmul Tag.E7.rank
        (ladd Tag.E7.rank (lpow Tag.E7.rank e7O8WList 4) (lid Tag.E7.rank))
        (ladd Tag.E7.rank (lpow Tag.E7.rank e7O8WList 2) (lsmul Tag.E7.rank (-1)
          (lid Tag.E7.rank)))) := by
      rw [toMat_lmul, toMat_ladd, toMat_ladd, toMat_lpow, toMat_lpow, toMat_lsmul_neg_one,
        toMat_lid, e7O8W_eq, sub_eq_add_neg]
    rw [h, e7O8V_eq, ← toVec_lmulVec]
    decide +kernel
  · rw [e7O8W_eq, e7O8Alpha_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [e7O8W_eq, e7O8Beta_eq, e7O8Gamma_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [e7O8W_eq, e7O8Beta_eq, e7O8Gamma_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [e7O8W_eq, e7O8Beta_eq, e7O8V_eq, e7O8Alpha_eq, ← toMat_lpow, ← toVec_lmulVec]
    decide +kernel
  · rw [e7O8W_eq, e7O8Gamma_eq, e7O8V_eq, e7O8Alpha_eq, ← toMat_lpow, ← toVec_lmulVec,
      ← toVec_lmulVec]
    decide +kernel
  · have hmem : ∀ l ∈ [e7O8AlphaList, e7O8BetaList, e7O8GammaList], l ∈ Tag.E7.artifactRoots := by
      decide +kernel
    have hlen : ∀ i : Fin 3, [e7O8AlphaList, e7O8BetaList, e7O8GammaList].getD i [] ∈
        [e7O8AlphaList, e7O8BetaList, e7O8GammaList] := by
      decide +kernel
    intro i
    rw [hABG]
    exact isRoot_toVec (hmem _ (hlen i))
  ·
    have hdet : IsUnit (Matrix.of fun i (j : Fin Tag.E7.rank) => e7O8Ext j i).det := by
      rw [hExt, of_cols_eq_toMat, det_toMat_eq]
      rw [show CFSG.LieType.Chevalley.laplaceDet Tag.E7.rank (toMat Tag.E7.rank
        (lcols Tag.E7.rank e7O8ExtList)) = 1 by decide +kernel]
      exact isUnit_one
    have hli : LinearIndependent ℤ e7O8Ext := by
      have := (Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E7.rank))).2 (by
        rw [Module.Basis.det_apply]
        exact hdet)
      exact this.1
    have h3 : e7O8ABG = e7O8Ext ∘ (Fin.castLE (by decide) : Fin 3 → Fin Tag.E7.rank) := by
      funext i
      fin_cases i <;> rfl
    rw [h3]
    exact hli.comp _ (Fin.castLE_injective _)
  · rw [hExt, of_cols_eq_toMat, det_toMat_eq]
    decide +kernel
  · have h := toMat_lgram .E7 (toMat_cartanList .E7) 3
      [e7O8AlphaList, e7O8BetaList, e7O8GammaList]
    rw [hABG]
    refine h.symm.trans ?_
    decide +kernel
  · ext c
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert c
    rw [hABG, ← toMat_cartanList]
    decide +kernel

end CFSG.RankThree.Lattice
