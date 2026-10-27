module

public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel
public import CFSG.RankThree.Lattice.SteinbergBIWeylMembership

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial

@[expose] def e7O5W : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ := wordMat .E7 [0, 2, 3, 4]

@[expose] def e7O5Alpha : Fin Tag.E7.rank → ℤ := ![0, 0, 0, 0, 0, 0, 1]

@[expose] def e7O5Theta : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 3, 2, 1, 0]

@[expose] def e7O5Beta : Fin Tag.E7.rank → ℤ := ![-1, -1, -2, -3, -2, -1, 0]

@[expose] def e7O5Cols : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  fun j => if (j : ℕ) = 0 then e7O5Alpha else if (j : ℕ) = 1 then e7O5Theta else
    (e7O5W ^ ((j : ℕ) - 2)) *ᵥ e7O5Beta

@[expose] def e7O5V : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  wordMat .E7 [1, 3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3]

@[expose] def e7O5Frame : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 1, 2, 1, 0, 0], ![0, 1, 1, 2, 2, 2, 1], ![2, 2, 3, 4, 3, 2, 1]]

@[expose] def e7O5AlphaList : List ℤ := [0, 0, 0, 0, 0, 0, 1]

@[expose] def e7O5ThetaList : List ℤ := [1, 2, 2, 3, 2, 1, 0]

@[expose] def e7O5BetaList : List ℤ := [-1, -1, -2, -3, -2, -1, 0]

@[expose] def e7O5AlphaThetaList : List ℤ := [1, 2, 2, 3, 2, 1, 1]

@[expose] def e7O5FrameList : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0],
    [0, 1, 1, 2, 1, 0, 0], [0, 1, 1, 2, 2, 2, 1], [2, 2, 3, 4, 3, 2, 1]]

@[expose] def e7O5WList : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1, 0], [0, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, -1, 1, 0], [0, 1, 1, 0, -1, 1, 0],
   [0, 0, 0, 1, -1, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7O5BasisInv : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, -1, 0], [-1, 1, 1, -1, 0, 0, 0], [1, 0, -1, 1, -1, 0, 0],
   [0, 0, 1, -1, 1, -1, 0], [-1, 0, 0, 1, -1, 0, 0], [1, 0, -1, 0, 1, -1, 0]]

@[expose] def e7O5BasisOps : List (ℕ × ℕ × ℤ) :=
  [(1, 0, 1), (0, 1, -1), (1, 0, 1), (0, 2, 1), (0, 5, 1), (0, 6, 1), (2, 1, 1), (1, 2, -1),
   (2, 1, 1), (1, 3, 1), (1, 4, 1), (1, 5, -1), (1, 6, -1), (3, 2, 1), (2, 3, -1), (3, 2, 1),
   (2, 5, 1), (4, 3, 1), (3, 4, -1), (4, 3, 1), (3, 6, 1), (5, 4, 1), (4, 5, -1), (5, 4, 1),
   (6, 5, 1), (5, 6, -1), (6, 5, 1)]

@[expose] def e7O5Rows : List KernelRow := [
  { rep := [-2, -2, -3, -4, -3, -2, -1], fc := [-1, 0],
    f := [1, 0, 0, 1, 0], h := [1, 1, 1, 0], d := 1,
    q := [0, 1],
    orbit := [[-2, -2, -3, -4, -3, -2, -1], [-1, -2, -3, -4, -3, -2, -1],
       [-1, -2, -2, -4, -3, -2, -1], [-1, -2, -2, -3, -3, -2, -1], [-1, -2, -2, -3, -2, -2, -1],
       [2, 2, 3, 4, 3, 2, 1], [1, 2, 3, 4, 3, 2, 1], [1, 2, 2, 4, 3, 2, 1], [1, 2, 2, 3, 3, 2, 1],
       [1, 2, 2, 3, 2, 2, 1]] },
  { rep := [-1, -1, -2, -3, -3, -2, -1], fc := [-1, 1],
    f := [1, 1, 0, 1, 0], h := [0, -1, -1, -1], d := 1,
    q := [-1, 0, -1],
    orbit := [[-1, -1, -2, -3, -3, -2, -1], [0, -1, -1, -2, -2, -2, -1],
       [-1, -1, -1, -2, -2, -2, -1], [-1, -1, -2, -2, -2, -2, -1], [-1, -1, -2, -3, -2, -2, -1],
       [1, 1, 2, 3, 3, 2, 1], [0, 1, 1, 2, 2, 2, 1], [1, 1, 1, 2, 2, 2, 1], [1, 1, 2, 2, 2, 2, 1],
       [1, 1, 2, 3, 2, 2, 1]] },
  { rep := [-1, -1, -2, -3, -2, -1, -1], fc := [-1, 0],
    f := [1, 0, 0, 0, 0], h := [1, 0, 0, 0], d := 1,
    q := [],
    orbit := [[-1, -1, -2, -3, -2, -1, -1], [0, -1, -1, -2, -2, -1, -1], [0, -1, 0, -1, -1, -1, -1],
       [-1, -1, -1, -1, -1, -1, -1], [-1, -1, -2, -2, -1, -1, -1], [1, 1, 2, 3, 2, 1, 1],
       [0, 1, 1, 2, 2, 1, 1], [0, 1, 0, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1],
       [1, 1, 2, 2, 1, 1, 1]] },
  { rep := [-1, -1, -2, -3, -2, -1, 0], fc := [0, 0],
    f := [1, 0, 0, 0, 0], h := [1, 0, 0, 0], d := 1,
    q := [],
    orbit := [[-1, -1, -2, -3, -2, -1, 0], [0, -1, -1, -2, -2, -1, 0], [0, -1, 0, -1, -1, -1, 0],
       [-1, -1, -1, -1, -1, -1, 0], [-1, -1, -2, -2, -1, -1, 0], [1, 1, 2, 3, 2, 1, 0],
       [0, 1, 1, 2, 2, 1, 0], [0, 1, 0, 1, 1, 1, 0], [1, 1, 1, 1, 1, 1, 0],
       [1, 1, 2, 2, 1, 1, 0]] },
  { rep := [-1, -1, -2, -2, -2, -1, -1], fc := [-1, 0],
    f := [0, 1, -1, 1, 0], h := [1, 1, 0, -1], d := 1,
    q := [-1, 2, -1],
    orbit := [[-1, -1, -2, -2, -2, -1, -1], [0, -1, -1, -2, -1, -1, -1],
       [-1, -1, -1, -2, -2, -1, -1], [0, -1, -1, -1, -1, -1, -1], [-1, -1, -1, -2, -1, -1, -1],
       [1, 1, 2, 2, 2, 1, 1], [0, 1, 1, 2, 1, 1, 1], [1, 1, 1, 2, 2, 1, 1], [0, 1, 1, 1, 1, 1, 1],
       [1, 1, 1, 2, 1, 1, 1]] },
  { rep := [-1, -1, -2, -2, -2, -1, 0], fc := [0, 0],
    f := [0, 1, -1, 1, 0], h := [1, 1, 0, -1], d := 1,
    q := [-1, 2, -1],
    orbit := [[-1, -1, -2, -2, -2, -1, 0], [0, -1, -1, -2, -1, -1, 0], [-1, -1, -1, -2, -2, -1, 0],
       [0, -1, -1, -1, -1, -1, 0], [-1, -1, -1, -2, -1, -1, 0], [1, 1, 2, 2, 2, 1, 0],
       [0, 1, 1, 2, 1, 1, 0], [1, 1, 1, 2, 2, 1, 0], [0, 1, 1, 1, 1, 1, 0],
       [1, 1, 1, 2, 1, 1, 0]] },
  { rep := [-1, -1, -2, -2, -1, 0, 0], fc := [0, -1],
    f := [0, 0, -1, 0, 0], h := [0, 0, 0, -1], d := 1,
    q := [-1, 1],
    orbit := [[-1, -1, -2, -2, -1, 0, 0], [0, -1, -1, -2, -1, 0, 0], [0, -1, 0, -1, -1, 0, 0],
       [0, -1, 0, 0, 0, 0, 0], [-1, -1, -1, -1, 0, 0, 0], [1, 1, 2, 2, 1, 0, 0],
       [0, 1, 1, 2, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0],
       [1, 1, 1, 1, 0, 0, 0]] },
  { rep := [-1, -1, -1, -2, -1, 0, 0], fc := [0, -1],
    f := [1, -1, 0, 0, -1], h := [1, 0, -1, -1], d := 1,
    q := [0, -1, 0, 1],
    orbit := [[-1, -1, -1, -2, -1, 0, 0], [0, -1, -1, -1, -1, 0, 0], [0, -1, 0, -1, 0, 0, 0],
       [-1, -1, -1, -1, -1, 0, 0], [0, -1, -1, -1, 0, 0, 0], [1, 1, 1, 2, 1, 0, 0],
       [0, 1, 1, 1, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [1, 1, 1, 1, 1, 0, 0],
       [0, 1, 1, 1, 0, 0, 0]] },
  { rep := [-1, 0, -1, -1, -1, -1, -1], fc := [-1, 1],
    f := [1, 0, 0, 1, 0], h := [1, 1, 1, 0], d := 1,
    q := [0, 1],
    orbit := [[-1, 0, -1, -1, -1, -1, -1], [0, 0, -1, -1, -1, -1, -1], [0, 0, 0, -1, -1, -1, -1],
       [0, 0, 0, 0, -1, -1, -1], [0, 0, 0, 0, 0, -1, -1], [1, 0, 1, 1, 1, 1, 1],
       [0, 0, 1, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1],
       [0, 0, 0, 0, 0, 1, 1]] },
  { rep := [-1, 0, -1, -1, -1, -1, 0], fc := [0, 1],
    f := [1, 0, 0, 1, 0], h := [1, 1, 1, 0], d := 1,
    q := [0, 1],
    orbit := [[-1, 0, -1, -1, -1, -1, 0], [0, 0, -1, -1, -1, -1, 0], [0, 0, 0, -1, -1, -1, 0],
       [0, 0, 0, 0, -1, -1, 0], [0, 0, 0, 0, 0, -1, 0], [1, 0, 1, 1, 1, 1, 0],
       [0, 0, 1, 1, 1, 1, 0], [0, 0, 0, 1, 1, 1, 0], [0, 0, 0, 0, 1, 1, 0],
       [0, 0, 0, 0, 0, 1, 0]] },
  { rep := [-1, 0, -1, -1, -1, 0, 0], fc := [0, 0],
    f := [1, 0, -1, 1, -1], h := [3, 1, -1, -3], d := 5,
    q := [-2, 3, -5, 3],
    orbit := [[-1, 0, -1, -1, -1, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 1, 0, 0], [-1, 0, 0, 0, 0, 0, 0],
       [0, 0, -1, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0]] },
  { rep := [-1, 0, -1, -1, 0, 0, 0], fc := [0, 0],
    f := [1, -1, 0, 0, 0], h := [4, 3, 2, 1], d := 5,
    q := [-1],
    orbit := [[-1, 0, -1, -1, 0, 0, 0], [0, 0, -1, -1, -1, 0, 0], [1, 0, 1, 0, 0, 0, 0],
       [0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0],
       [-1, 0, -1, 0, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0], [0, 0, 0, -1, -1, 0, 0]] }]

@[expose] def e7NegOneWord : List ℕ :=
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5,
   1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2, 1, 0]

@[expose] def e7O5Basis : List (List ℤ) :=
  lcols Tag.E7.rank (e7O5AlphaList :: e7O5ThetaList :: lorbit Tag.E7.rank e7O5WList e7O5BetaList 5)

@[expose] def e7O5Conj : List (List ℤ) :=
  lmul Tag.E7.rank (lmul Tag.E7.rank e7O5BasisInv e7O5WList) e7O5Basis

@[expose] def e7O5ConjNeg : List (List ℤ) :=
  lmul Tag.E7.rank (lmul Tag.E7.rank e7O5BasisInv (lsmul Tag.E7.rank (-1) e7O5WList)) e7O5Basis

theorem e7O5W_eq : e7O5W = toMat Tag.E7.rank e7O5WList :=
  wordMat_eq_toMat .E7 _ (by decide +kernel)

theorem e7O5Alpha_eq : e7O5Alpha = toVec Tag.E7.rank e7O5AlphaList := by decide +kernel

theorem e7O5Theta_eq : e7O5Theta = toVec Tag.E7.rank e7O5ThetaList := by decide +kernel

theorem e7O5Beta_eq : e7O5Beta = toVec Tag.E7.rank e7O5BetaList := by decide +kernel

theorem e7O5Cols_eq' : e7O5Cols = fun j : Fin Tag.E7.rank => toVec Tag.E7.rank
    ((e7O5AlphaList :: e7O5ThetaList ::
      lorbit Tag.E7.rank e7O5WList e7O5BetaList 5).getD j []) := by
  have h := cols_ite_two_eq (n := Tag.E7.rank) e7O5WList e7O5AlphaList e7O5ThetaList
    e7O5BetaList 5
  rw [← e7O5Alpha_eq, ← e7O5Theta_eq, ← e7O5Beta_eq, ← e7O5W_eq] at h
  exact h

theorem e7O5Cols_eq :
    (Matrix.of fun i (j : Fin Tag.E7.rank) => e7O5Cols j i) = toMat Tag.E7.rank e7O5Basis := by
  rw [e7O5Basis, ← of_cols_eq_toMat, e7O5Cols_eq']

theorem e7O5Basis_mul_inv : lmul Tag.E7.rank e7O5Basis e7O5BasisInv = lid Tag.E7.rank := by
  decide +kernel

theorem e7O5_det_basis : (toMat Tag.E7.rank e7O5Basis).det = 1 := by
  rw [det_toMat_eq_of_colAdds _ e7O5BasisOps (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem e7O5Frame_eq :
    e7O5Frame = fun i : Fin Tag.E7.rank => toVec Tag.E7.rank (e7O5FrameList.getD i []) := by
  decide +kernel

theorem e7O5Conj_blocks :
    lowerLeftZero 2 5 e7O5Conj = true ∧ ltopLeft 2 e7O5Conj = [[1, 0], [0, 1]] ∧
      lbotRight 2 5 e7O5Conj = [[0, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0],
        [0, 0, 1, 0, 0], [0, 0, 0, 1, 0]] := by
  decide +kernel

theorem e7O5ConjNeg_blocks :
    lowerLeftZero 2 5 e7O5ConjNeg = true ∧ ltopLeft 2 e7O5ConjNeg = [[-1, 0], [0, -1]] ∧
      lbotRight 2 5 e7O5ConjNeg = [[0, 0, 0, 0, -1], [-1, 0, 0, 0, 0], [0, -1, 0, 0, 0],
        [0, 0, -1, 0, 0], [0, 0, 0, -1, 0]] := by
  decide +kernel

theorem charpoly_e7O5W : e7O5W.charpoly = (X - 1) ^ 2 * (X ^ 5 - 1) := by
  have hc : (toMat Tag.E7.rank e7O5WList).charpoly = (toMat Tag.E7.rank e7O5Conj).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E7.rank e7O5Basis)
      (B' := toMat Tag.E7.rank e7O5BasisInv)
      (by rw [← toMat_lmul, e7O5Basis_mul_inv, toMat_lid]), e7O5Conj, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e7O5Conj_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 2) (m := 5) e7O5Conj h₁
  rw [h₂, h₃, charpoly_toMat_two_diag, map_one] at hb
  rw [e7O5W_eq, hc]
  refine Eq.trans (hb : (toMat Tag.E7.rank e7O5Conj).charpoly = _) (congrArg _ ?_)
  exact charpoly_eq_of_lists (cs := [-1, 0, 0, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 5) (by decide +kernel))

theorem charpoly_neg_e7O5W : (-e7O5W).charpoly = (X + 1) ^ 2 * (X ^ 5 + 1) := by
  have hc : (toMat Tag.E7.rank (lsmul Tag.E7.rank (-1) e7O5WList)).charpoly =
      (toMat Tag.E7.rank e7O5ConjNeg).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E7.rank e7O5Basis)
      (B' := toMat Tag.E7.rank e7O5BasisInv)
      (by rw [← toMat_lmul, e7O5Basis_mul_inv, toMat_lid]), e7O5ConjNeg, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e7O5ConjNeg_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 2) (m := 5) e7O5ConjNeg h₁
  rw [h₂, h₃, charpoly_toMat_two_diag, show (C (-1 : ℤ)) = -1 by simp, sub_neg_eq_add] at hb
  rw [e7O5W_eq, ← toMat_lsmul_neg_one, hc]
  refine Eq.trans (hb : (toMat Tag.E7.rank e7O5ConjNeg).charpoly = _) (congrArg _ ?_)
  exact charpoly_eq_of_lists (cs := [1, 0, 0, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0, 0]
    (by
      rw [orbitMat_eq_toMat]
      exact isUnit_det_of_lmul_eq_lid (N := lcols 5 (lorbit 5 [[0, 0, 0, 0, -1],
        [-1, 0, 0, 0, 0], [0, -1, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, -1, 0]]
          [1, 0, 0, 0, 0] 5)) (by decide +kernel))

theorem e7O5_root_kernel (p : ℕ) [Fact p.Prime] (hp5 : 5 < p) (a : ZMod p)
    (ha : a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0) (z : Fin Tag.E7.rank → ZMod p)
    (hz0 : z ≠ 0) (hz : (e7O5W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z) :
    {r | IsRoot .E7 r ∧ pair r z = 0} =
      {e7O5Alpha, -e7O5Alpha, e7O5Theta, -e7O5Theta, e7O5Alpha + e7O5Theta,
        -(e7O5Alpha + e7O5Theta)} := by
  rw [e7O5W_eq] at hz
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
  have hα : pair (toVec Tag.E7.rank e7O5AlphaList) z = 0 :=
    pair_eq_zero_of_fixed hz ha1 (by rw [← toVec_lmulVec]; exact congrArg _ (by decide +kernel))
  have hθ : pair (toVec Tag.E7.rank e7O5ThetaList) z = 0 :=
    pair_eq_zero_of_fixed hz ha1 (by rw [← toVec_lmulVec]; exact congrArg _ (by decide +kernel))
  have hαθ : pair (toVec Tag.E7.rank e7O5AlphaThetaList) z = 0 := by
    have h : toVec Tag.E7.rank e7O5AlphaThetaList =
        toVec Tag.E7.rank e7O5AlphaList + toVec Tag.E7.rank e7O5ThetaList := by
      decide +kernel
    rw [h, pair_add, hα, hθ, add_zero]
  have hβ : pair (toVec Tag.E7.rank e7O5BetaList) z ≠ 0 := by
    intro h0
    apply hz0
    refine eq_zero_of_pair_cols_eq_zero (B := toMat Tag.E7.rank e7O5Basis)
      (by rw [e7O5_det_basis]; exact isUnit_one) fun j => ?_
    have hcol : (fun i => toMat Tag.E7.rank e7O5Basis i j) = toVec Tag.E7.rank
        ((e7O5AlphaList :: e7O5ThetaList ::
          lorbit Tag.E7.rank e7O5WList e7O5BetaList 5).getD j []) := by
      rw [← e7O5Cols_eq]
      exact congrFun e7O5Cols_eq' j
    rw [hcol, getD_cons_eq_ite, getD_cons_eq_ite]
    have hj : (j : ℕ) < 7 := j.isLt
    split_ifs with h h'
    · exact hα
    · exact hθ
    · rw [toVec_lorbit_getD (by omega), pair_pow_mulVec hz, h0, mul_zero]
  have hd : ∀ r ∈ e7O5Rows, 0 < r.d ∧ r.d ≤ 5 := by decide +kernel
  have hker := rootKernel_eq_of_rows (τ := .E7) (F := [e7O5AlphaList, e7O5ThetaList])
    (β := e7O5BetaList) (Φ := [1, 1, 1, 1, 1]) (m := 5) (signed := true) e7O5Rows
    [e7O5AlphaList, vneg Tag.E7.rank e7O5AlphaList, e7O5ThetaList, vneg Tag.E7.rank e7O5ThetaList,
      e7O5AlphaThetaList, vneg Tag.E7.rank e7O5AlphaThetaList]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hz ha0 hΦ
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hα
      · exact hθ) hβ
    (fun r hr => intCast_zmod_ne_zero (hd r hr).1 (by
      have h2 : (5 : ℤ) < p := by exact_mod_cast hp5
      have := (hd r hr).2
      omega))
    (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hα
      · rw [toVec_vneg, pair_neg, hα]
        exact neg_zero
      · exact hθ
      · rw [toVec_vneg, pair_neg, hθ]
        exact neg_zero
      · exact hαθ
      · rw [toVec_vneg, pair_neg, hαθ]
        exact neg_zero)
  refine hker.trans ?_
  have hsum : e7O5Alpha + e7O5Theta = toVec Tag.E7.rank e7O5AlphaThetaList := by decide +kernel
  ext r
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Set.mem_insert_iff, Set.mem_singleton_iff, toVec_vneg, ← e7O5Alpha_eq,
    ← e7O5Theta_eq, hsum]

theorem E7_order_five_lattice_and_exact_A2_prime_root_kernel :
    IsRoot .E7 e7O5Alpha ∧ IsRoot .E7 e7O5Theta ∧ IsRoot .E7 e7O5Beta ∧
    e7O5Alpha ⬝ᵥ (Tag.E7.cartan *ᵥ e7O5Theta) = -1 ∧ orderOf e7O5W = 5 ∧
    e7O5W *ᵥ e7O5Alpha = e7O5Alpha ∧ e7O5W *ᵥ e7O5Theta = e7O5Theta ∧
    (LinearIndependent ℤ e7O5Cols ∧ Submodule.span ℤ (Set.range e7O5Cols) = ⊤) ∧
    (Matrix.of fun i (j : Fin Tag.E7.rank) => e7O5Cols j i).det = 1 ∧
    e7O5W.charpoly = (X - 1) ^ 2 * (X ^ 5 - 1) ∧
    (-e7O5W).charpoly = (X + 1) ^ 2 * (X ^ 5 + 1) ∧
    (∀ p : ℕ, p.Prime → 5 < p → ∀ a : ZMod p, a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0 →
      ∀ z : Fin Tag.E7.rank → ZMod p, z ≠ 0 →
        (e7O5W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z →
        {r | IsRoot .E7 r ∧ pair r z = 0} =
          {e7O5Alpha, -e7O5Alpha, e7O5Theta, -e7O5Theta, e7O5Alpha + e7O5Theta,
            -(e7O5Alpha + e7O5Theta)}) ∧
    e7O5V *ᵥ Pi.single 0 1 = e7O5Alpha ∧ e7O5V *ᵥ Pi.single 2 1 = e7O5Theta ∧
    (∀ i, IsRoot .E7 (e7O5Frame i)) ∧ gramMat .E7 e7O5Frame = 2 ∧
    (List.ofFn fun i => rootReflMat .E7 (e7O5Frame i)).prod = -1 ∧
    (-1 : (Module.End ℤ (Fin Tag.E7.rank → ℤ))ˣ) ∈ CFSG.LieType.Chevalley.latticeWeylGroup .E7 := by
  have hV : e7O5V = toMat Tag.E7.rank (lword Tag.E7.rank (cartanList .E7)
      [1, 3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3]) :=
    wordMat_eq_toMat .E7 _ rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, charpoly_e7O5W, charpoly_neg_e7O5W,
    fun p hp hp5 a ha z hz0 hz => @e7O5_root_kernel p ⟨hp⟩ hp5 a ha z hz0 hz, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [e7O5Alpha_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e7O5Theta_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e7O5Beta_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e7O5Alpha_eq, e7O5Theta_eq, ← toMat_cartanList, ← toVec_lmulVec]
    decide +kernel
  · rw [e7O5W_eq]
    exact orderOf_toMat_eq (by norm_num) (by decide +kernel) (by decide +kernel)
  · rw [e7O5W_eq, e7O5Alpha_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [e7O5W_eq, e7O5Theta_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E7.rank)), Module.Basis.det_apply]
    have h : (Pi.basisFun ℤ (Fin Tag.E7.rank)).toMatrix e7O5Cols =
        Matrix.of fun i (j : Fin Tag.E7.rank) => e7O5Cols j i := rfl
    rw [h, e7O5Cols_eq, e7O5_det_basis]
    exact isUnit_one
  · rw [e7O5Cols_eq, e7O5_det_basis]
  · rw [hV, e7O5Alpha_eq, show (Pi.single 0 1 : Fin Tag.E7.rank → ℤ) =
      toVec Tag.E7.rank [1, 0, 0, 0, 0, 0, 0] by decide +kernel, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [hV, e7O5Theta_eq, show (Pi.single 2 1 : Fin Tag.E7.rank → ℤ) =
      toVec Tag.E7.rank [0, 0, 1, 0, 0, 0, 0] by decide +kernel, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · have hmem : ∀ l ∈ e7O5FrameList, l ∈ Tag.E7.artifactRoots := by decide +kernel
    have hlen : ∀ i : Fin Tag.E7.rank, e7O5FrameList.getD i [] ∈ e7O5FrameList := by
      decide +kernel
    intro i
    rw [e7O5Frame_eq]
    exact isRoot_toVec (hmem _ (hlen i))
  · have h := toMat_lgram .E7 (toMat_cartanList .E7) Tag.E7.rank e7O5FrameList
    rw [e7O5Frame_eq]
    refine h.symm.trans ?_
    decide +kernel
  · rw [e7O5Frame_eq, prod_rootReflMat_eq .E7 (k := Tag.E7.rank) e7O5FrameList, prod_map_toMat,
      neg_one_eq_toMat]
    exact congrArg _ (by decide +kernel)
  · refine neg_one_mem_latticeWeylGroup (e7NegOneWord.map fun i => (Fin.ofNat _ i)) ?_
    rw [wordMat_eq_toMat .E7 _ rfl, neg_one_eq_toMat]
    exact congrArg _ (by decide +kernel)

end CFSG.RankThree.Lattice
