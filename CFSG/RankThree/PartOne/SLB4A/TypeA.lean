module

public import CFSG.RankThree.PartOne.SLB4A.Sign
public import CFSG.RankThree.PartOne.SLB4A.Unip

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

theorem exists_two_pow_five_psl_odd (n : ℕ) (hn : 7 ≤ n) (h2 : (-1 : K) ≠ 1) :
    ∃ U : Subgroup (StatedProj (StatedSL n K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_sign_seven h2 (fun j : Fin 7 => (⟨j.1, by omega⟩ : Fin n)) ?_ _ ?_
  · intro i j h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro v hv
    refine Subgroup.subset_closure ?_
    show ((signD K v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1
    rw [det_signD, hv, eps_one]

theorem exists_two_pow_five_psl_six (h2 : (-1 : K) ≠ 1) (u : Kˣ) (hu : (u : K) * u = -1) :
    ∃ U : Subgroup (StatedProj (StatedSL 6 K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_sign_six h2 u (fun j : Fin 6 => j) (fun i j h => h) _ ?_ ?_
  · intro v hv
    refine Subgroup.subset_closure ?_
    show ((signD K v : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1
    rw [det_signD, hv, eps_one]
  · intro v hv
    refine Subgroup.subset_closure ?_
    show (((Matrix.GeneralLinearGroup.scalar (Fin 6) u * signD K v : GL (Fin 6) K)) :
      Matrix (Fin 6) (Fin 6) K).det = 1
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_mul, det_signD, hv,
      eps_gen, Matrix.scalar_apply, Matrix.det_diagonal]
    have h6 : (u : K) ^ 6 = -1 := by
      calc (u : K) ^ 6 = ((u : K) * u) ^ 3 := by ring
        _ = (-1) ^ 3 := by rw [hu]
        _ = -1 := by norm_num
    simp [Finset.prod_const, h6]

def rowIx (k : Fin 5) : ℕ := (![0, 0, 0, 1, 1] : Fin 5 → ℕ) k

def colIx (k : Fin 5) : ℕ := (![2, 3, 4, 2, 3] : Fin 5 → ℕ) k

theorem rowIx_lt (k : Fin 5) : rowIx k < 2 := by
  fin_cases k <;> simp [rowIx]

theorem colIx_range (k : Fin 5) : 2 ≤ colIx k ∧ colIx k < 5 := by
  fin_cases k <;> simp [colIx]

theorem rowIx_colIx_ne (k l : Fin 5) : colIx k ≠ rowIx l := by
  have := rowIx_lt l
  have := colIx_range k
  omega

theorem rowIx_colIx_inj (k l : Fin 5) (h1 : rowIx k = rowIx l) (h2 : colIx k = colIx l) : k = l := by
  fin_cases k <;> fin_cases l <;> simp_all [rowIx, colIx]

theorem exists_two_pow_five_psl_even [CharP K 2] (n : ℕ) (hn : 5 ≤ n) :
    ∃ U : Subgroup (StatedProj (StatedSL n K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  let a : Fin 5 → Fin n := fun k => ⟨rowIx k, by have := rowIx_lt k; omega⟩
  let b : Fin 5 → Fin n := fun k => ⟨colIx k, by have := colIx_range k; omega⟩
  let X : Fin 5 → Matrix (Fin n) (Fin n) K := fun k => Matrix.single (a k) (b k) 1
  have hX : ∀ k l, X k * X l = 0 := fun k l => by
    have hne : b k ≠ a l := fun h => rowIx_colIx_ne k l (by simpa [a, b, Fin.ext_iff] using h)
    ext i j
    simp only [Matrix.mul_apply, X, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : a k = i ∧ b k = x
    · have : ¬ (a l = x ∧ b l = j) := fun ⟨h2, _⟩ => hne (h1.2.trans h2.symm)
      simp [this]
    · simp [h1]
  refine exists_two_pow_five_unip hX ?_ _ ?_
  · intro v ⟨c, hc⟩
    refine funext fun k => cC2_eq_zero (K := K) _ ?_ (one_ne_zero : (1 : K) ≠ 0)
    have h := congrFun (congrFun hc (a k)) (b k)
    have hab : a k ≠ b k := fun h => by
      have := rowIx_lt k
      have := colIx_range k
      simp [a, b, Fin.ext_iff] at h
      omega
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab] at h
    rw [← h]
    simp only [Xsum, X, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      have : ¬ (a l = a k ∧ b l = b k) := fun ⟨h1, h2⟩ => hl (rowIx_colIx_inj l k
        (by simpa [a, Fin.ext_iff] using h1) (by simpa [b, Fin.ext_iff] using h2))
      simp [this]
    · simp
  · intro k
    refine Subgroup.subset_closure ?_
    exact det_uniMat hX _

end CFSG.RankThree.PartOne.SLB4A
