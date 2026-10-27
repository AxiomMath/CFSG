module

public import CFSG.RankThree.PartOne.SLB4A.Sign

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank Matrix

section SpOdd

variable {K : Type} [Field K] {r : ℕ}

@[expose] def kr (a : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin r) (Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.fromBlocks (a 0 0 • D) (a 0 1 • D) (a 1 0 • D) (a 1 1 • D)

theorem kr_mul (a a' : Matrix (Fin 2) (Fin 2) K) (D D' : Matrix (Fin r) (Fin r) K) :
    kr a D * kr a' D' = kr (a * a') (D * D') := by
  simp only [kr, Matrix.fromBlocks_multiply, smul_mul_smul_comm, Matrix.mul_apply,
    Fin.sum_univ_two, ← add_smul]

theorem kr_one : kr (1 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin r) (Fin r) K) = 1 := by
  simp [kr, Matrix.fromBlocks_one]

theorem kr_transpose (a : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin r) (Fin r) K) :
    (kr a D)ᵀ = kr aᵀ Dᵀ := by
  simp [kr, Matrix.fromBlocks_transpose]

@[expose] def J2 : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem kr_J2 : kr (J2 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin r) (Fin r) K) =
    Matrix.fromBlocks 0 1 (-1) 0 := by
  simp [kr, J2]

theorem J2_mul_J2 : (J2 : Matrix (Fin 2) (Fin 2) K) * J2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def jM (x y : K) : Matrix (Fin 2) (Fin 2) K := !![x, y; y, -x]

theorem jM_mul_jM {x y : K} (hxy : x * x + y * y = -1) : jM x y * jM x y = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jM, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hxy

theorem jM_mul_J2 (x y : K) : jM x y * J2 = -(J2 * jM x y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jM, J2, Matrix.mul_apply, Fin.sum_univ_two]

theorem kr_symplectic (a : Matrix (Fin 2) (Fin 2) K) (hdet : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1)
    (D : Matrix (Fin r) (Fin r) K) (hD : Dᵀ * D = 1) :
    (kr a D)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * kr a D = Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [← kr_J2, kr_transpose, kr_mul, kr_mul]
  have h1 : aᵀ * J2 * a = J2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hdet | linear_combination -hdet
  rw [h1, mul_one, hD]

@[expose] def Dk (k : ℕ) : Matrix (Fin r) (Fin r) K :=
  Matrix.diagonal fun a => if a.1 = k then -1 else 1

theorem Dk_mul_self (k : ℕ) : (Dk k : Matrix (Fin r) (Fin r) K) * Dk k = 1 := by
  rw [Dk, Matrix.diagonal_mul_diagonal]
  have : ∀ a : Fin r, ((if a.1 = k then (-1 : K) else 1) * if a.1 = k then -1 else 1) = 1 := by
    intro a
    split_ifs <;> simp
  simp only [this]
  exact Matrix.diagonal_one

theorem Dk_transpose (k : ℕ) : (Dk k : Matrix (Fin r) (Fin r) K)ᵀ = Dk k := by
  rw [Dk, Matrix.diagonal_transpose]

@[expose] def krGL (a a' : Matrix (Fin 2) (Fin 2) K) (D D' : Matrix (Fin r) (Fin r) K)
    (h1 : a * a' = 1) (h2 : a' * a = 1) (h3 : D * D' = 1) (h4 : D' * D = 1) :
    GL (Fin r ⊕ Fin r) K :=
  ⟨kr a D, kr a' D', by rw [kr_mul, h1, h3, kr_one], by rw [kr_mul, h2, h4, kr_one]⟩

theorem kr_pow (a : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin r) (Fin r) K) (n : ℕ) :
    (kr a D) ^ n = kr (a ^ n) (D ^ n) := by
  induction n with
  | zero => simp [kr_one]
  | succ n ih => rw [pow_succ, ih, kr_mul, pow_succ, pow_succ]

theorem kr_smul_left (c : K) (a : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin r) (Fin r) K) :
    kr (c • a) D = c • kr a D := by
  simp [kr, Matrix.fromBlocks_smul, mul_smul]

variable (x y : K)

@[expose] def qA : Fin 5 → Matrix (Fin 2) (Fin 2) K := ![J2, jM x y, 1, 1, 1]

@[expose] def qA' : Fin 5 → Matrix (Fin 2) (Fin 2) K := ![-J2, -jM x y, 1, 1, 1]

@[expose] def qD (r : ℕ) : Fin 5 → Matrix (Fin r) (Fin r) K := ![1, 1, Dk 0, Dk 1, Dk 2]

variable {x y}

theorem qA_mul_qA' (hxy : x * x + y * y = -1) (k : Fin 5) : qA x y k * qA' x y k = 1 := by
  fin_cases k
  · simp [qA, qA', J2_mul_J2]
  · simp [qA, qA', jM_mul_jM hxy]
  all_goals simp [qA, qA']

theorem qA'_mul_qA (hxy : x * x + y * y = -1) (k : Fin 5) : qA' x y k * qA x y k = 1 := by
  fin_cases k
  · simp [qA, qA', J2_mul_J2]
  · simp [qA, qA', jM_mul_jM hxy]
  all_goals simp [qA, qA']

theorem qD_mul_qD (k : Fin 5) : qD (K := K) r k * qD r k = 1 := by
  fin_cases k
  all_goals simp [qD, Dk_mul_self]

@[expose] def spOddElt (hxy : x * x + y * y = -1) (k : Fin 5) : GL (Fin r ⊕ Fin r) K :=
  krGL (qA x y k) (qA' x y k) (qD r k) (qD r k) (qA_mul_qA' hxy k) (qA'_mul_qA hxy k)
    (qD_mul_qD k) (qD_mul_qD k)

theorem coe_spOddElt (hxy : x * x + y * y = -1) (k : Fin 5) :
    ((spOddElt (r := r) hxy k : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      kr (qA x y k) (qD r k) :=
  rfl

theorem spOddElt_mem (hxy : x * x + y * y = -1) (k : Fin 5) :
    spOddElt (r := r) hxy k ∈ StatedSp r K := by
  refine Subgroup.subset_closure ?_
  show ((spOddElt (r := r) hxy k : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
    ((spOddElt (r := r) hxy k : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = Matrix.fromBlocks 0 1 (-1) 0
  rw [coe_spOddElt]
  refine kr_symplectic _ ?_ _ ?_
  · fin_cases k
    · simp [qA, J2]
    · simp [qA, jM]
      linear_combination -hxy
    all_goals simp [qA]
  · fin_cases k
    all_goals simp [qD, Dk_transpose, Dk_mul_self]

theorem Dk_comm (k l : ℕ) : (Dk k : Matrix (Fin r) (Fin r) K) * Dk l = Dk l * Dk k := by
  rw [Dk, Dk, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem qD_comm (i j : Fin 5) : qD (K := K) r i * qD r j = qD r j * qD r i := by
  fin_cases i <;> fin_cases j <;> simp [qD, Dk_comm]

theorem qA_comm (i j : Fin 5) :
    ∃ c : K, c ≠ 0 ∧ qA x y j * qA x y i = c • (qA x y i * qA x y j) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | (refine ⟨1, one_ne_zero, ?_⟩; simp [qA]; done)
    | (refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩; simp [qA, jM_mul_J2])

theorem qA_sq (hxy : x * x + y * y = -1) (i : Fin 5) :
    ∃ c : K, c ≠ 0 ∧ qA x y i * qA x y i = c • 1 := by
  fin_cases i
  · exact ⟨-1, neg_ne_zero.2 one_ne_zero, by simp [qA, J2_mul_J2]⟩
  · exact ⟨-1, neg_ne_zero.2 one_ne_zero, by simp [qA, jM_mul_jM hxy]⟩
  all_goals exact ⟨1, one_ne_zero, by simp [qA]⟩

theorem spOddElt_comm (hxy : x * x + y * y = -1) (i j : Fin 5) :
    (spOddElt (r := r) hxy i * spOddElt hxy j)⁻¹ * (spOddElt hxy j * spOddElt hxy i) ∈
      StatedScalars (Fin r ⊕ Fin r) K := by
  obtain ⟨c, hc0, hc⟩ := qA_comm (x := x) (y := y) i j
  refine inv_mul_mem_scalars _ _ c hc0 ?_
  simp only [Units.val_mul, coe_spOddElt, kr_mul]
  rw [hc, ← qD_comm j i, kr_smul_left]

theorem spOddElt_sq (hxy : x * x + y * y = -1) (k : Fin 5) :
    spOddElt (r := r) hxy k * spOddElt hxy k ∈ StatedScalars (Fin r ⊕ Fin r) K := by
  obtain ⟨c, hc0, hc⟩ := qA_sq hxy (x := x) (y := y) k
  refine mem_scalars_of_eq_smul_one _ c hc0 ?_
  simp only [Units.val_mul, coe_spOddElt, kr_mul]
  rw [hc, qD_mul_qD, kr_smul_left, kr_one]

theorem kr_diag_scalar {a : Matrix (Fin 2) (Fin 2) K} {d : Fin r → K} {c : K}
    (h : kr a (Matrix.diagonal d) = Matrix.scalar (Fin r ⊕ Fin r) c) :
    (∀ i, a 0 1 * d i = 0) ∧ (∀ i, a 1 0 * d i = 0) ∧ (∀ i, a 0 0 * d i = c) ∧
      ∀ i, a 1 1 * d i = c := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
    simpa [kr, Matrix.scalar_apply] using this
  · have := congrFun (congrFun h (Sum.inr i)) (Sum.inl i)
    simpa [kr, Matrix.scalar_apply] using this
  · have := congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
    simpa [kr, Matrix.scalar_apply] using this
  · have := congrFun (congrFun h (Sum.inr i)) (Sum.inr i)
    simpa [kr, Matrix.scalar_apply] using this

@[expose] def dval (v : V2 5) (a : Fin r) : K :=
  (if a.1 = 0 then eps K (v 2) else 1) * (if a.1 = 1 then eps K (v 3) else 1) *
    (if a.1 = 2 then eps K (v 4) else 1)

theorem Dk_pow (k n : ℕ) : (Dk k : Matrix (Fin r) (Fin r) K) ^ n =
    Matrix.diagonal fun a => if a.1 = k then (-1 : K) ^ n else 1 := by
  rw [Dk, Matrix.diagonal_pow]
  congr 1
  funext a
  by_cases h : a.1 = k <;> simp [h]

theorem Dprod (v : V2 5) :
    (Dk 0 : Matrix (Fin r) (Fin r) K) ^ ex (v 2) * Dk 1 ^ ex (v 3) * Dk 2 ^ ex (v 4) =
      Matrix.diagonal (dval v) := by
  rw [Dk_pow, Dk_pow, Dk_pow, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  rfl

theorem dval_ne_zero (v : V2 5) (a : Fin r) : (dval v a : K) ≠ 0 := by
  have h : ∀ x : C2, eps K x ≠ 0 := fun x h0 => by
    have := eps_mul_self K x
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  unfold dval
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> split_ifs <;> first | exact h _ | exact one_ne_zero

theorem spOddProd_coe (hxy : x * x + y * y = -1) (v : V2 5) :
    ((spOddElt (r := r) hxy 0 ^ ex (v 0) * spOddElt hxy 1 ^ ex (v 1) * spOddElt hxy 2 ^ ex (v 2) *
      spOddElt hxy 3 ^ ex (v 3) * spOddElt hxy 4 ^ ex (v 4) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      kr (J2 ^ ex (v 0) * jM x y ^ ex (v 1)) (Matrix.diagonal (dval v)) := by
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_spOddElt, kr_pow, kr_mul]
  simp only [qA, qD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_pow, mul_one,
    one_mul]
  rw [Dprod]

theorem exists_two_pow_five_psp_odd (hr : 4 ≤ r) (h2 : (-1 : K) ≠ 1) {x y : K}
    (hxy : x * x + y * y = -1) :
    ∃ U : Subgroup (StatedProj (StatedSp r K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_statedProj_inv _ (spOddElt hxy) (spOddElt_mem hxy)
    (spOddElt_comm hxy) (spOddElt_sq hxy) ?_
  intro v hv
  obtain ⟨c, hc⟩ := mem_statedScalars_iff.1 hv
  rw [spOddProd_coe] at hc
  obtain ⟨h01, h10, h00, h11⟩ := kr_diag_scalar hc
  have hd := dval_ne_zero (K := K) (r := r) v
  have two_ne : (2 : K) ≠ 0 := fun h => h2 (by linear_combination -h)
  have d3 : dval v (⟨3, by omega⟩ : Fin r) = (1 : K) := by simp [dval]
  have d0 : dval v (⟨0, by omega⟩ : Fin r) = eps K (v 2) := by simp [dval]
  have d1 : dval v (⟨1, by omega⟩ : Fin r) = eps K (v 3) := by simp [dval]
  have d2 : dval v (⟨2, by omega⟩ : Fin r) = eps K (v 4) := by simp [dval]
  rcases ex_cases (v 0) with h0 | h0 <;> rcases ex_cases (v 1) with h1 | h1
  ·
    rw [h0, h1] at h00
    simp only [pow_zero, mul_one] at h00
    have c1 : c = 1 := by simpa [d3] using (h00 ⟨3, by omega⟩).symm
    have e2 : v 2 = 1 := by
      have := h00 ⟨0, by omega⟩
      rw [d0, c1] at this
      simp at this
      exact eps_inj h2 (this.trans (eps_one K).symm)
    have e3 : v 3 = 1 := by
      have := h00 ⟨1, by omega⟩
      rw [d1, c1] at this
      simp at this
      exact eps_inj h2 (this.trans (eps_one K).symm)
    have e4 : v 4 = 1 := by
      have := h00 ⟨2, by omega⟩
      rw [d2, c1] at this
      simp at this
      exact eps_inj h2 (this.trans (eps_one K).symm)
    funext k
    fin_cases k
    · exact eq_one_of_ex_eq_zero h0
    · exact eq_one_of_ex_eq_zero h1
    · exact e2
    · exact e3
    · exact e4
  ·
    rw [h0, h1] at h01 h00 h11
    have hy : y = 0 := by
      have := h01 ⟨0, by omega⟩
      simp [jM] at this
      rcases this with h | h
      · exact h
      · exact absurd h (hd ⟨0, by omega⟩)
    have a := h00 ⟨3, by omega⟩
    have b := h11 ⟨3, by omega⟩
    simp [jM, d3] at a b
    have hx : x = 0 := by
      have : (2 : K) * x = 0 := by linear_combination a - b
      exact (mul_eq_zero.1 this).resolve_left two_ne
    rw [hx, hy] at hxy
    simp at hxy
  ·
    rw [h0, h1] at h01
    have := h01 ⟨0, by omega⟩
    simp [J2] at this
    exact absurd this (hd ⟨0, by omega⟩)
  ·
    rw [h0, h1] at h01 h00 h11
    have hx : x = 0 := by
      have := h01 ⟨0, by omega⟩
      simp [J2, jM, Matrix.mul_apply, Fin.sum_univ_two] at this
      rcases this with h | h
      · exact h
      · exact absurd h (hd ⟨0, by omega⟩)
    have a := h00 ⟨3, by omega⟩
    have b := h11 ⟨3, by omega⟩
    simp [J2, jM, Matrix.mul_apply, Fin.sum_univ_two, d3] at a b
    have hy : y = 0 := by
      have : (2 : K) * y = 0 := by linear_combination a - b
      exact (mul_eq_zero.1 this).resolve_left two_ne
    rw [hx, hy] at hxy
    simp at hxy

end SpOdd

theorem exists_sq_add_sq_neg_one (K : Type) [Field K] [Finite K] (h : Nat.card K % 2 = 1) :
    ∃ x y : K, x * x + y * y = -1 := by
  have := Fintype.ofFinite K
  have hch : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 : Polynomial K)) (g := Polynomial.X ^ 2 + 1) (by compute_degree!)
    (by compute_degree!) hch
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one] at hab
  exact ⟨a, b, by linear_combination hab⟩

end CFSG.RankThree.PartOne.SLB4A
