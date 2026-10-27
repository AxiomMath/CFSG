module

public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial

@[expose] def e6O5W : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := wordMat .E6 [0, 2, 3, 4]

@[expose] def e6O5Theta : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def e6O5Beta : Fin Tag.E6.rank → ℤ := ![-1, -1, -2, -3, -2, -1]

@[expose] def e6O5Cols : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  fun j => if (j : ℕ) = 0 then e6O5Theta else (e6O5W ^ ((j : ℕ) - 1)) *ᵥ e6O5Beta

@[expose] def e6O5ThetaList : List ℤ := [1, 2, 2, 3, 2, 1]

@[expose] def e6O5BetaList : List ℤ := [-1, -1, -2, -3, -2, -1]

@[expose] def e6O5WList : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1], [0, 1, 0, 0, 0, 0], [1, 1, 0, 0, -1, 1], [0, 1, 1, 0, -1, 1],
   [0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def e6O5BasisInv : List (List ℤ) :=
  [[0, 1, 0, 0, 0, -1], [-1, 1, 1, -1, 0, 0], [1, 0, -1, 1, -1, 0], [0, 0, 1, -1, 1, -1],
   [-1, 0, 0, 1, -1, 0], [1, 0, -1, 0, 1, -1]]

@[expose] def e6O5BasisOps : List (ℕ × ℕ × ℤ) :=
  [(0, 1, 1), (0, 4, 1), (0, 5, 1), (1, 2, 1), (1, 3, 1), (1, 4, -1), (1, 5, -1), (2, 4, 1),
   (3, 5, 1)]

@[expose] def e6O5Rows : List KernelRow := [
  { rep := [-1, -1, -2, -3, -2, -1], fc := [0],
    f := [1, 0, 0, 0, 0], h := [1, 0, 0, 0], d := 1,
    q := [],
    orbit := [[-1, -1, -2, -3, -2, -1], [0, -1, -1, -2, -2, -1], [0, -1, 0, -1, -1, -1],
       [-1, -1, -1, -1, -1, -1], [-1, -1, -2, -2, -1, -1], [1, 1, 2, 3, 2, 1], [0, 1, 1, 2, 2, 1],
       [0, 1, 0, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 2, 2, 1, 1]] },
  { rep := [-1, -1, -2, -2, -2, -1], fc := [0],
    f := [0, 1, -1, 1, 0], h := [1, 1, 0, -1], d := 1,
    q := [-1, 2, -1],
    orbit := [[-1, -1, -2, -2, -2, -1], [0, -1, -1, -2, -1, -1], [-1, -1, -1, -2, -2, -1],
       [0, -1, -1, -1, -1, -1], [-1, -1, -1, -2, -1, -1], [1, 1, 2, 2, 2, 1], [0, 1, 1, 2, 1, 1],
       [1, 1, 1, 2, 2, 1], [0, 1, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1]] },
  { rep := [-1, -1, -2, -2, -1, 0], fc := [-1],
    f := [0, 0, -1, 0, 0], h := [0, 0, 0, -1], d := 1,
    q := [-1, 1],
    orbit := [[-1, -1, -2, -2, -1, 0], [0, -1, -1, -2, -1, 0], [0, -1, 0, -1, -1, 0],
       [0, -1, 0, 0, 0, 0], [-1, -1, -1, -1, 0, 0], [1, 1, 2, 2, 1, 0], [0, 1, 1, 2, 1, 0],
       [0, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0]] },
  { rep := [-1, -1, -1, -2, -1, 0], fc := [-1],
    f := [1, -1, 0, 0, -1], h := [1, 0, -1, -1], d := 1,
    q := [0, -1, 0, 1],
    orbit := [[-1, -1, -1, -2, -1, 0], [0, -1, -1, -1, -1, 0], [0, -1, 0, -1, 0, 0],
       [-1, -1, -1, -1, -1, 0], [0, -1, -1, -1, 0, 0], [1, 1, 1, 2, 1, 0], [0, 1, 1, 1, 1, 0],
       [0, 1, 0, 1, 0, 0], [1, 1, 1, 1, 1, 0], [0, 1, 1, 1, 0, 0]] },
  { rep := [-1, 0, -1, -1, -1, -1], fc := [1],
    f := [1, 0, 0, 1, 0], h := [1, 1, 1, 0], d := 1,
    q := [0, 1],
    orbit := [[-1, 0, -1, -1, -1, -1], [0, 0, -1, -1, -1, -1], [0, 0, 0, -1, -1, -1],
       [0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, -1], [1, 0, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1],
       [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1]] },
  { rep := [-1, 0, -1, -1, -1, 0], fc := [0],
    f := [1, 0, -1, 1, -1], h := [3, 1, -1, -3], d := 5,
    q := [-2, 3, -5, 3],
    orbit := [[-1, 0, -1, -1, -1, 0], [1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0],
       [0, 0, 0, 0, 1, 0], [1, 0, 1, 1, 1, 0], [-1, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0],
       [0, 0, 0, -1, 0, 0], [0, 0, 0, 0, -1, 0]] },
  { rep := [-1, 0, -1, -1, 0, 0], fc := [0],
    f := [1, -1, 0, 0, 0], h := [4, 3, 2, 1], d := 5,
    q := [-1],
    orbit := [[-1, 0, -1, -1, 0, 0], [0, 0, -1, -1, -1, 0], [1, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 0],
       [0, 0, 0, 1, 1, 0], [1, 0, 1, 1, 0, 0], [0, 0, 1, 1, 1, 0], [-1, 0, -1, 0, 0, 0],
       [0, 0, -1, -1, 0, 0], [0, 0, 0, -1, -1, 0]] }]

@[expose] def e6O5Basis : List (List ℤ) :=
  lcols Tag.E6.rank (e6O5ThetaList :: lorbit Tag.E6.rank e6O5WList e6O5BetaList 5)

@[expose] def e6O5Conj : List (List ℤ) :=
  lmul Tag.E6.rank (lmul Tag.E6.rank e6O5BasisInv e6O5WList) e6O5Basis

theorem e6O5W_eq : e6O5W = toMat Tag.E6.rank e6O5WList :=
  wordMat_eq_toMat .E6 _ (by decide +kernel)

theorem e6O5Theta_eq : e6O5Theta = toVec Tag.E6.rank e6O5ThetaList := by decide +kernel

theorem e6O5Beta_eq : e6O5Beta = toVec Tag.E6.rank e6O5BetaList := by decide +kernel

theorem e6O5Cols_eq' : e6O5Cols = fun j : Fin Tag.E6.rank => toVec Tag.E6.rank
    ((e6O5ThetaList :: lorbit Tag.E6.rank e6O5WList e6O5BetaList 5).getD j []) := by
  have h := cols_ite_eq (n := Tag.E6.rank) e6O5WList e6O5ThetaList e6O5BetaList 5
  rw [← e6O5Theta_eq, ← e6O5Beta_eq, ← e6O5W_eq] at h
  exact h

theorem e6O5Cols_eq :
    (Matrix.of fun i (j : Fin Tag.E6.rank) => e6O5Cols j i) = toMat Tag.E6.rank e6O5Basis := by
  rw [e6O5Basis, ← of_cols_eq_toMat, e6O5Cols_eq']

theorem e6O5Basis_mul_inv : lmul Tag.E6.rank e6O5Basis e6O5BasisInv = lid Tag.E6.rank := by
  decide +kernel

theorem e6O5_det_basis : (toMat Tag.E6.rank e6O5Basis).det = 1 := by
  rw [det_toMat_eq_of_colAdds _ e6O5BasisOps (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem charpoly_one_by_one' (c : ℤ) : (toMat 1 [[c]]).charpoly = X - C c := by
  have h : toMat 1 [[c]] = Matrix.diagonal fun _ => c := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [h, Matrix.charpoly_diagonal, Fin.prod_univ_one]

theorem e6O5Conj_blocks :
    lowerLeftZero 1 5 e6O5Conj = true ∧ ltopLeft 1 e6O5Conj = [[1]] ∧
      lbotRight 1 5 e6O5Conj = [[0, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0],
        [0, 0, 1, 0, 0], [0, 0, 0, 1, 0]] := by
  decide +kernel

theorem charpoly_e6O5W : e6O5W.charpoly = (X - 1) * (X ^ 5 - 1) := by
  have hc : (toMat Tag.E6.rank e6O5WList).charpoly = (toMat Tag.E6.rank e6O5Conj).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E6.rank e6O5Basis)
      (B' := toMat Tag.E6.rank e6O5BasisInv)
      (by rw [← toMat_lmul, e6O5Basis_mul_inv, toMat_lid]), e6O5Conj, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e6O5Conj_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 1) (m := 5) e6O5Conj h₁
  rw [h₂, h₃, charpoly_one_by_one', map_one] at hb
  rw [e6O5W_eq, hc]
  refine Eq.trans (hb : (toMat Tag.E6.rank e6O5Conj).charpoly = _) (congrArg _ ?_)
  exact charpoly_eq_of_lists (cs := [-1, 0, 0, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 5) (by decide +kernel))

theorem e6O5_root_kernel (p : ℕ) [Fact p.Prime] (hp5 : 5 < p) (a : ZMod p)
    (ha : a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0) (z : Fin Tag.E6.rank → ZMod p)
    (hz0 : z ≠ 0) (hz : (e6O5W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z) :
    {α | IsRoot .E6 α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} := by
  rw [e6O5W_eq] at hz
  have hΦ : peval [1, 1, 1, 1, 1] a = 0 := by
    simp only [peval_cons, peval_nil, Int.cast_one]
    linear_combination ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h5 : ((5 : ℤ) : ZMod p) ≠ 0 := intCast_zmod_ne_zero (by norm_num) (by exact_mod_cast hp5)
    apply h5
    push_cast
    linear_combination ha
  have hθ : pair (toVec Tag.E6.rank e6O5ThetaList) z = 0 :=
    pair_eq_zero_of_fixed hz ha1 (by rw [← toVec_lmulVec]; exact congrArg _ (by decide +kernel))
  have hβ : pair (toVec Tag.E6.rank e6O5BetaList) z ≠ 0 := by
    intro h0
    apply hz0
    refine eq_zero_of_pair_cols_eq_zero (B := toMat Tag.E6.rank e6O5Basis)
      (by rw [e6O5_det_basis]; exact isUnit_one) fun j => ?_
    have hcol : (fun i => toMat Tag.E6.rank e6O5Basis i j) = toVec Tag.E6.rank ((e6O5ThetaList ::
        lorbit Tag.E6.rank e6O5WList e6O5BetaList 5).getD j []) := by
      rw [← e6O5Cols_eq]
      exact congrFun e6O5Cols_eq' j
    rw [hcol, getD_cons_eq_ite]
    have hj : (j : ℕ) < 6 := j.isLt
    split_ifs with h
    · exact hθ
    · rw [toVec_lorbit_getD (by omega), pair_pow_mulVec hz, h0, mul_zero]
  have hd : ∀ r ∈ e6O5Rows, 0 < r.d ∧ r.d ≤ 5 := by decide +kernel
  have hker := rootKernel_eq_of_rows (τ := .E6) (F := [e6O5ThetaList]) (β := e6O5BetaList)
    (Φ := [1, 1, 1, 1, 1]) (m := 5) (signed := true) e6O5Rows
    [e6O5ThetaList, vneg Tag.E6.rank e6O5ThetaList] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hz ha0 hΦ (by simpa using hθ) hβ
    (fun r hr => intCast_zmod_ne_zero (hd r hr).1 (by
      have h2 : (5 : ℤ) < p := by exact_mod_cast hp5
      have := (hd r hr).2
      omega))
    (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact hθ
      · rw [toVec_vneg, pair_neg, hθ]
        exact neg_zero)
  refine hker.trans ?_
  ext α
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Set.mem_insert_iff, Set.mem_singleton_iff, e6O5Theta_eq, toVec_vneg]

theorem E6_order_five_lattice_and_exact_A1_prime_root_kernel :
    IsRoot .E6 e6O5Theta ∧ IsRoot .E6 e6O5Beta ∧ orderOf e6O5W = 5 ∧
    e6O5W *ᵥ e6O5Theta = e6O5Theta ∧
    (LinearIndependent ℤ e6O5Cols ∧ Submodule.span ℤ (Set.range e6O5Cols) = ⊤) ∧
    (Matrix.of fun i (j : Fin Tag.E6.rank) => e6O5Cols j i).det = 1 ∧
    e6O5W.charpoly = (X - 1) * (X ^ 5 - 1) ∧
    (∀ i ∈ ({0, 2, 3, 4} : Finset (Fin Tag.E6.rank)),
      e6O5Theta ⬝ᵥ (Tag.E6.cartan *ᵥ Pi.single i 1) = 0) ∧
    ∀ p : ℕ, p.Prime → 5 < p → ∀ a : ZMod p, a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0 →
      ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
        (e6O5W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z →
        {α | IsRoot .E6 α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, charpoly_e6O5W, ?_,
    fun p hp hp5 a ha z hz0 hz => @e6O5_root_kernel p ⟨hp⟩ hp5 a ha z hz0 hz⟩
  · rw [e6O5Theta_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e6O5Beta_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e6O5W_eq]
    exact orderOf_toMat_eq (by norm_num) (by decide +kernel) (by decide +kernel)
  · rw [e6O5W_eq, e6O5Theta_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E6.rank)), Module.Basis.det_apply]
    have h : (Pi.basisFun ℤ (Fin Tag.E6.rank)).toMatrix e6O5Cols =
        Matrix.of fun i (j : Fin Tag.E6.rank) => e6O5Cols j i := rfl
    rw [h, e6O5Cols_eq, e6O5_det_basis]
    exact isUnit_one
  · rw [e6O5Cols_eq, e6O5_det_basis]
  · rw [e6O5Theta_eq]
    decide +kernel

end CFSG.RankThree.Lattice
