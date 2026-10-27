module

public import CFSG.RankThree.PartOne.KF1514B.Param
public import CFSG.RankThree.PartOne.KF1514B.Rank

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail QuadraticMap Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

theorem two_eq_zero_K : (2 : K) = 0 := CharTwo.two_eq_zero

theorem add_self_K (x : K) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem neg_K (x : K) : -x = x := CharTwo.neg_eq x

theorem uMap_zero_zero : uMap (minusTailForm K b c) (0 : Fin 3 → Fin 2 → K) 0 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [uMap_apply]
  refine Prod.ext (funext fun i => ?_) ?_
  · rcases i with i | i
    · rw [uLin_apply_inl, sMat_zero]
      simp
    · rfl
  · rw [uLin_apply_snd]
    simp

theorem conjL_one (L : Fin 3 → Fin 2 → K) : conjL (1 : GL (Fin 3) K) (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) L = L := by
  funext j
  simp [conjL, Matrix.one_apply]

theorem conjC_one (L : Fin 3 → Fin 2 → K) (C : Matrix (Fin 3) (Fin 3) K) :
    conjC (minusTailForm K b c) (1 : GL (Fin 3) K) (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) L C = C := by
  simp [conjC, conjL_one]

theorem conjL_zero (D : GL (Fin 3) K) : conjL D (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (0 : Fin 3 → Fin 2 → K) = 0 := by
  funext j
  simp [conjL]

theorem mulParam_zero_right (L : Fin 3 → Fin 2 → K) (C C' : Matrix (Fin 3) (Fin 3) K) :
    mulParam (minusTailForm K b c) L 0 C C' = C + C' := by
  simp only [mulParam, sMat_zero, crossMat]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, QuadraticMap.polar_zero_right]
  ring

theorem mulParam_zero_left (L : Fin 3 → Fin 2 → K) (C C' : Matrix (Fin 3) (Fin 3) K) :
    mulParam (minusTailForm K b c) 0 L C C' = C + C' := by
  simp only [mulParam, sMat_zero, crossMat, zero_add]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, QuadraticMap.polar_zero_left]
  ring

theorem isPar_one : IsPar (b := b) (c := c) (1 : Vt K ≃ₗ[K] Vt K) 1 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    rw [Units.val_one]
    exact Matrix.one_apply_ne (ne_of_gt h)
  · intro i
    rw [Units.val_one, Matrix.one_apply_eq]
  · simp
  · intro i; rfl
  · rw [dMap_one_one, uMap_zero_zero, one_mul]

theorem Dm_one : Dm (1 : ↥(U0 b c)) = 1 :=
  (par_eq (g := 1) (by simpa using isPar_one (b := b) (c := c))).1

theorem Lp_one : Lp (1 : ↥(U0 b c)) = 0 :=
  (par_eq (g := 1) (by simpa using isPar_one (b := b) (c := c))).2.1

theorem Cp_one : Cp (1 : ↥(U0 b c)) = 0 :=
  (par_eq (g := 1) (by simpa using isPar_one (b := b) (c := c))).2.2

theorem dc_one : dc (1 : ↥(U0 b c)) = 0 := by
  simp [dc, Dm_one]

theorem da_mul_db_of_sq {g : ↥(U0 b c)} (h : g * g = 1) : da g * db g = 0 := by
  have h1 : dc (g * g) = dc g + dc g + da g * db g := dc_mul g g
  rw [h, dc_one, add_self_K, zero_add] at h1
  exact h1.symm

theorem da_db_comm {g g' : ↥(U0 b c)} (h : g * g' = g' * g) :
    da g * db g' = da g' * db g := by
  have h1 := dc_mul g g'
  have h2 := dc_mul g' g
  rw [h] at h1
  linear_combination h2 - h1


theorem polar_minusTail (v w : Fin 2 → K) :
    QuadraticMap.polar (minusTailForm K b c) v w = b * det2 v w := by
  simp only [QuadraticMap.polar, minusTailForm_apply, det2, Pi.add_apply]
  linear_combination (v 0 * w 0 + b * v 1 * w 0 + c * v 1 * w 1) * (two_eq_zero_K (K := K))

theorem b_ne_zero {b c : K} [AnisoPair b c] : b ≠ 0 := by
  intro hb
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  refine AnisoPair.hirr (b := b) (c := c) s ?_
  rw [hb, hs]
  linear_combination (s * s) * (two_eq_zero_K (K := K))

theorem polar_eq_zero_iff (v w : Fin 2 → K) :
    QuadraticMap.polar (minusTailForm K b c) v w = 0 ↔ det2 v w = 0 := by
  rw [polar_minusTail]
  exact ⟨fun h => (mul_eq_zero.1 h).resolve_left (b_ne_zero (b := b) (c := c)), fun h => by rw [h, mul_zero]⟩

theorem Lp_mul_of_Dm_one {n n' : ↥(U0 b c)} (hn' : Dm n' = 1) : Lp (n * n') = Lp n + Lp n' := by
  have h := (par_eq (g := n * n') (IsPar.mul (par_spec n) (par_spec n'))).2.1
  rw [hn', inv_one, conjL_one] at h
  exact h

theorem inv_entries (D : GL (Fin 3) K) (hup : (D : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (hd : ∀ i, (D : Matrix (Fin 3) (Fin 3) K) i i = 1) :
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 ∧
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = (D : Matrix (Fin 3) (Fin 3) K) 0 1 ∧
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = (D : Matrix (Fin 3) (Fin 3) K) 1 2 ∧
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 =
      (D : Matrix (Fin 3) (Fin 3) K) 0 1 * (D : Matrix (Fin 3) (Fin 3) K) 1 2 +
        (D : Matrix (Fin 3) (Fin 3) K) 0 2 ∧
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  have hDE : (D : Matrix (Fin 3) (Fin 3) K) * ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    Units.mul_inv D
  have e : ∀ i j, ((D : Matrix (Fin 3) (Fin 3) K) * ((D⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j := fun i j => by
    rw [hDE]
  set E : Matrix (Fin 3) (Fin 3) K := ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hE
  have h10 : (D : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := hup (show (0 : Fin 3) < 1 by decide)
  have h20 : (D : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := hup (show (0 : Fin 3) < 2 by decide)
  have h21 : (D : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := hup (show (1 : Fin 3) < 2 by decide)
  have d0 := hd 0
  have d1 := hd 1
  have d2 := hd 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, d0, d1, d2]
    at e20 e21 e22 e10 e11 e12 e00 e01 e02
  have E20 : E 2 0 = 0 := e20
  have E21 : E 2 1 = 0 := e21
  have E22 : E 2 2 = 1 := e22
  have E10 : E 1 0 = 0 := by rw [E20] at e10; simpa using e10
  have E11 : E 1 1 = 1 := by rw [E21] at e11; simpa using e11
  have E00 : E 0 0 = 1 := by rw [E10, E20] at e00; simpa using e00
  have E12 : E 1 2 = (D : Matrix (Fin 3) (Fin 3) K) 1 2 := by
    rw [E22] at e12
    have : E 1 2 + (D : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by simpa using e12
    linear_combination this - (D : Matrix (Fin 3) (Fin 3) K) 1 2 * (two_eq_zero_K (K := K))
  have E01 : E 0 1 = (D : Matrix (Fin 3) (Fin 3) K) 0 1 := by
    rw [E11, E21] at e01
    have : E 0 1 + (D : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by simpa using e01
    linear_combination this - (D : Matrix (Fin 3) (Fin 3) K) 0 1 * (two_eq_zero_K (K := K))
  have E02 : E 0 2 = (D : Matrix (Fin 3) (Fin 3) K) 0 1 * (D : Matrix (Fin 3) (Fin 3) K) 1 2 +
      (D : Matrix (Fin 3) (Fin 3) K) 0 2 := by
    rw [E12, E22] at e02
    have : E 0 2 + (D : Matrix (Fin 3) (Fin 3) K) 0 1 * (D : Matrix (Fin 3) (Fin 3) K) 1 2 +
        (D : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by simpa using e02
    linear_combination this - ((D : Matrix (Fin 3) (Fin 3) K) 0 1 * (D : Matrix (Fin 3) (Fin 3) K) 1 2 +
        (D : Matrix (Fin 3) (Fin 3) K) 0 2) * (two_eq_zero_K (K := K))
  exact ⟨E00, E11, E22, E01, E12, E02, E10, E20, E21⟩


theorem Lp_fixed {g n : ↥(U0 b c)} (hn : Dm n = 1) (h : g * n = n * g) :
    Lp n = conjL (Dm g)⁻¹ 1 (Lp n) := by
  have h1 := (par_eq (g := g * n) (IsPar.mul (par_spec g) (par_spec n))).2.1
  have h2 := (par_eq (g := n * g) (IsPar.mul (par_spec n) (par_spec g))).2.1
  rw [h] at h1
  rw [hn, inv_one, conjL_one] at h1
  have h3 : Lp g + Lp n = conjL (Dm g)⁻¹ 1 (Lp n) + Lp g := h1.symm.trans h2
  exact add_right_cancel (by rw [add_comm (Lp n) (Lp g)]; exact h3)

theorem Lp_constraints {g n : ↥(U0 b c)} (hn : Dm n = 1) (h : g * n = n * g) :
    da g • Lp n 1 + (da g * db g + dc g) • Lp n 2 = 0 ∧ db g • Lp n 2 = 0 := by
  have hfix := Lp_fixed hn h
  obtain ⟨E00, E11, E22, E01, E12, E02, E10, E20, E21⟩ :=
    inv_entries (Dm g) (par_spec g).upper (par_spec g).diag
  have c0 : ∀ k, conjL (Dm g)⁻¹ 1 (Lp n) 0 k =
      Lp n 0 k + da g * Lp n 1 k + (da g * db g + dc g) * Lp n 2 k := by
    intro k
    simp only [conjL, LinearEquiv.coe_one, id_eq, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, E00, E01, E02, da, db, dc, one_mul]
  have c1 : ∀ k, conjL (Dm g)⁻¹ 1 (Lp n) 1 k = Lp n 1 k + db g * Lp n 2 k := by
    intro k
    simp only [conjL, LinearEquiv.coe_one, id_eq, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, E10, E11, E12, db, one_mul, zero_mul, zero_add]
  refine ⟨funext fun k => ?_, funext fun k => ?_⟩
  · have e := congrFun (congrFun hfix 0) k
    rw [c0 k] at e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination -e
  · have e := congrFun (congrFun hfix 1) k
    rw [c1 k] at e
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination -e


theorem add_self_fun (L : Fin 3 → Fin 2 → K) : L + L = 0 := by
  funext i k
  exact add_self_K _

theorem mulParam_self (L : Fin 3 → Fin 2 → K) (C : Matrix (Fin 3) (Fin 3) K) :
    mulParam (minusTailForm K b c) L L C C = crossMat (minusTailForm K b c) L L := by
  simp only [mulParam, add_self_fun, sMat_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
  have h2 := two_eq_zero_K (K := K)
  linear_combination (sMat (minusTailForm K b c) L i j + C i j -
    crossMat (minusTailForm K b c) L L i j) * h2

theorem Orth_Lp_of_sq {n : ↥(U0 b c)} (hn : Dm n = 1) (h : n * n = 1) : Orth (Lp n) := by
  have h1 := (par_eq (g := n * n) (IsPar.mul (par_spec n) (par_spec n))).2.2
  rw [h, Cp_one, hn, inv_one, conjL_one, conjC_one, mulParam_self] at h1
  intro i j
  have e := congrFun (congrFun h1 i) j
  simp only [crossMat, Matrix.of_apply, Matrix.zero_apply] at e
  exact (polar_eq_zero_iff (b := b) (c := c) _ _).1 e.symm


theorem conjC_zero_eq (D : GL (Fin 3) K) (C : Matrix (Fin 3) (Fin 3) K) :
    conjC (minusTailForm K b c) D (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (0 : Fin 3 → Fin 2 → K) C =
      (D : Matrix (Fin 3) (Fin 3) K) * C * (D : Matrix (Fin 3) (Fin 3) K)ᵀ := by
  simp [conjC, conjL_zero, sMat_zero]

theorem Cp_fixed {g z : ↥(U0 b c)} (hz : Dm z = 1) (hLz : Lp z = 0) (h : g * z = z * g) :
    Cp z = ((Dm g)⁻¹ : GL (Fin 3) K).val * Cp z * ((Dm g)⁻¹ : GL (Fin 3) K).valᵀ := by
  have h1 := (par_eq (g := g * z) (IsPar.mul (par_spec g) (par_spec z))).2.2
  have h2 := (par_eq (g := z * g) (IsPar.mul (par_spec z) (par_spec g))).2.2
  rw [h] at h1
  rw [hz, inv_one, conjL_one, conjC_one, hLz, mulParam_zero_right] at h1
  rw [hLz, conjL_zero, mulParam_zero_left, conjC_zero_eq] at h2
  have h3 : Cp g + Cp z = ((Dm g)⁻¹ : GL (Fin 3) K).val * Cp z * ((Dm g)⁻¹ : GL (Fin 3) K).valᵀ +
      Cp g := h1.symm.trans h2
  exact add_right_cancel (by rw [add_comm (Cp z) (Cp g)]; exact h3)

theorem Cp_constraints {g z : ↥(U0 b c)} (hz : Dm z = 1) (hLz : Lp z = 0) (h : g * z = z * g) :
    db g * Cp z 0 2 + dc g * Cp z 1 2 = 0 ∧ da g * Cp z 1 2 = 0 := by
  have hfix := Cp_fixed hz hLz h
  obtain ⟨E00, E11, E22, E01, E12, E02, E10, E20, E21⟩ :=
    inv_entries (Dm g) (par_spec g).upper (par_spec g).diag
  have hz' := par_spec z
  have hsym : ∀ i j, Cp z j i = Cp z i j := by
    intro i j
    have e := congrFun (congrFun hz'.alt i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at e
    rw [e]
    exact neg_K _
  have d0 := hz'.diag0 0
  have d1 := hz'.diag0 1
  have d2 := hz'.diag0 2
  have s10 := hsym 0 1
  have s20 := hsym 0 2
  have s21 := hsym 1 2
  have e01 := congrFun (congrFun hfix 0) 1
  have e02 := congrFun (congrFun hfix 0) 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, E00, E11, E22, E01, E12,
    E02, E10, E20, E21, d0, d1, d2, s10, s20, s21] at e01 e02
  have h2 := two_eq_zero_K (K := K)
  constructor
  · simp only [da, db, dc]
    linear_combination (-1 : K) * e01 - ((Dm g : Matrix (Fin 3) (Fin 3) K) 0 1 *
      (Dm g : Matrix (Fin 3) (Fin 3) K) 1 2 * Cp z 1 2) * h2
  · simp only [da]
    linear_combination (-1 : K) * e02

end CFSG.RankThree.PartOne.KF1514B
