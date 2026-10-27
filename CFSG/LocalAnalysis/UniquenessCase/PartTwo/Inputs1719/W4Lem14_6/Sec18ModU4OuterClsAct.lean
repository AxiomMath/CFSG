module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4OuterClsDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmSixMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.U4FF (NaturalSU4 NaturalOmega6 disp)
open CFSG.SeitzReduction.F4Pilot (omIsoGroup statedOmega_le_omIsoGroup)
open scoped commutatorElement Pointwise Matrix

private def adjStdVec {F : Type} [Field F] (r : Om6Idx) : Om6Idx → F := Pi.single r 1

private def wedgeTrace {F : Type} [Field F] (b : F) (X : Matrix Om6Idx Om6Idx F) : F :=
  (∑ i : Fin (3 - 1), X (.inl i) (.inr (.inl i))) + b * X (.inr (.inr 0)) (.inr (.inr 1))

private def adjGram {F : Type} [Field F] (c : F) : Matrix Om6Idx Om6Idx F :=
  (∑ i : Fin (3 - 1), wedgeM (adjStdVec (.inl i)) (adjStdVec (.inr (.inl i)))) +
    c • wedgeM (adjStdVec (.inr (.inr 0))) (adjStdVec (.inr (.inr 1)))

private lemma adjBinv_eq_adjGram {F : Type} [Field F] (b : F) :
    adjBinv b = adjGram b⁻¹ := rfl

private def adjTrace {F : Type} [Field F] (b : F) : Matrix Om6Idx Om6Idx F :=
  (∑ i : Fin (3 - 1),
      Matrix.vecMulVec (adjStdVec (.inr (.inl i))) (adjStdVec (.inl i))) +
    b • Matrix.vecMulVec (adjStdVec (.inr (.inr 1))) (adjStdVec (.inr (.inr 0)))

variable {F : Type} [Field F] [CharP F 2]

private lemma adjTrace_transpose_add (b : F) : adjTrace b + (adjTrace b)ᵀ = adjGram b := by
  have h1 : (adjTrace b)ᵀ =
      (∑ i : Fin (3 - 1),
          Matrix.vecMulVec (adjStdVec (.inl i)) (adjStdVec (.inr (.inl i)))) +
        b • Matrix.vecMulVec (adjStdVec (.inr (.inr 0))) (adjStdVec (.inr (.inr 1))) := by
    simp only [adjTrace, Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_smul,
      Matrix.transpose_vecMulVec]
  have hsum :
      (∑ i : Fin (3 - 1), Matrix.vecMulVec (adjStdVec (.inr (.inl i))) (adjStdVec (.inl i))) +
        (∑ i : Fin (3 - 1), Matrix.vecMulVec (adjStdVec (.inl i)) (adjStdVec (.inr (.inl i)))) =
      ∑ i : Fin (3 - 1), wedgeM (F := F) (adjStdVec (.inl i)) (adjStdVec (.inr (.inl i))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [wedgeM]
    exact add_comm _ _
  have hb :
      b • Matrix.vecMulVec (adjStdVec (.inr (.inr 1))) (adjStdVec (.inr (.inr 0))) +
        b • Matrix.vecMulVec (adjStdVec (.inr (.inr 0))) (adjStdVec (.inr (.inr 1))) =
      b • wedgeM (F := F) (adjStdVec (.inr (.inr 0))) (adjStdVec (.inr (.inr 1))) := by
    rw [wedgeM, smul_add, add_comm]
  rw [h1, adjTrace, adjGram, ← hsum, ← hb]
  abel

private lemma trace_vecMulVec_mul (u v : Om6Idx → F) (X : Matrix Om6Idx Om6Idx F) :
    (Matrix.vecMulVec u v * X).trace = v ⬝ᵥ (X *ᵥ u) := by
  have h1 : (Matrix.vecMulVec u v * X).trace = ∑ i, ∑ j, u i * v j * X j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have h2 : v ⬝ᵥ (X *ᵥ u) = ∑ i, ∑ j, v i * (X i j * u j) := by
    simp only [dotProduct, Matrix.mulVec_apply, Matrix.row_apply, Finset.mul_sum]
  rw [h1, h2, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma trace_adjTrace_mul (b : F) (X : Matrix Om6Idx Om6Idx F) :
    (adjTrace b * X).trace = wedgeTrace b X := by
  simp only [adjTrace, wedgeTrace, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, trace_vecMulVec_mul,
    adjStdVec, single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [smul_eq_mul]

private lemma quadraticPolar_eq_add (b c : F) (v w : Om6Idx → F) :
    QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) v w =
      StatedQuadMinus 3 F b c (v + w) + StatedQuadMinus 3 F b c v +
        StatedQuadMinus 3 F b c w := by
  rw [QuadraticMap.polar, CFSG.LieType.Universal.Spin.coe_quadMinus, CharTwo.sub_eq_add,
    CharTwo.sub_eq_add]

private lemma adjPolar_eq_polar (b c : F) (v w : Om6Idx → F) :
    adjPolar b v w = QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) v w := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus]
  simp only [adjPolar, CharTwo.two_eq_zero, zero_mul, zero_add, add_zero]

private lemma wedgeM_transpose (v w : Om6Idx → F) : (wedgeM v w)ᵀ = wedgeM v w := by
  simp only [wedgeM, Matrix.transpose_add, Matrix.transpose_vecMulVec]
  rw [add_comm]

private lemma adjBinv_transpose (b : F) : (adjBinv b)ᵀ = adjBinv b := by
  rw [adjBinv_eq_adjGram]
  simp only [adjGram, Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_smul,
    wedgeM_transpose]

private lemma add_mul_self_eq_zero (x y : F) : x * y + y * x = 0 := by
  rw [mul_comm y x, CharTwo.add_self_eq_zero]

private lemma wedgeM_diag (v w : Om6Idx → F) (i : Om6Idx) : wedgeM v w i i = 0 := by
  simp only [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, add_mul_self_eq_zero]

private lemma adjGram_diag (c : F) (i : Om6Idx) : adjGram c i i = 0 := by
  simp only [adjGram, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, wedgeM,
    Matrix.add_apply, Matrix.vecMulVec_apply, add_mul_self_eq_zero, Finset.sum_const_zero,
    zero_add, smul_eq_mul, mul_zero]

private lemma wedgeTrace_add (b : F) (X Y : Matrix Om6Idx Om6Idx F) :
    wedgeTrace b (X + Y) = wedgeTrace b X + wedgeTrace b Y := by
  simp only [wedgeTrace, Matrix.add_apply, Finset.sum_add_distrib]
  ring

private lemma wedgeTrace_smul (b : F) (c : F) (X : Matrix Om6Idx Om6Idx F) :
    wedgeTrace b (c • X) = c * wedgeTrace b X := by
  simp only [wedgeTrace, Matrix.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  ring

private lemma wedgeTrace_sum (s : Finset (Fin (3 - 1))) (b : F)
    (X : Fin (3 - 1) → Matrix Om6Idx Om6Idx F) :
    wedgeTrace b (∑ i ∈ s, X i) = ∑ i ∈ s, wedgeTrace b (X i) := by
  simp only [wedgeTrace, Matrix.sum_apply, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

private lemma wedgeTrace_wedgeM (b : F) (v w : Om6Idx → F) :
    wedgeTrace b (wedgeM v w) = adjPolar b v w := by
  simp only [wedgeTrace, adjPolar, wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply,
    Finset.sum_add_distrib, mul_add]

private lemma wedgeTrace_stdWedge (b : F) (i : Fin (3 - 1)) :
    adjPolar b (adjStdVec (.inl i)) (adjStdVec (.inr (.inl i))) = 1 := by
  simp [adjPolar, adjStdVec, Pi.single_apply, Finset.sum_ite_eq]

private lemma adjPolar_std_uv (b : F) :
    adjPolar b (adjStdVec (.inr (.inr 0))) (adjStdVec (.inr (.inr 1))) = b := by
  simp [adjPolar, adjStdVec, Pi.single_apply, Finset.sum_ite_eq]

private lemma wedgeTrace_adjBinv (b : F) (hb : b ≠ 0) : wedgeTrace b (adjBinv b) = 1 := by
  have h1 : wedgeTrace b (∑ i : Fin (3 - 1),
      wedgeM (adjStdVec (.inl i)) (adjStdVec (.inr (.inl i)))) = ∑ i : Fin (3 - 1), (1 : F) := by
    rw [wedgeTrace_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [wedgeTrace_wedgeM, wedgeTrace_stdWedge]
  have h2 : wedgeTrace b (wedgeM (adjStdVec (.inr (.inr 0))) (adjStdVec (.inr (.inr 1)))) = b := by
    rw [wedgeTrace_wedgeM, adjPolar_std_uv]
  rw [adjBinv_eq_adjGram, adjGram, wedgeTrace_add, h1, wedgeTrace_smul, h2]
  have hc : (∑ _i : Fin (3 - 1), (1 : F)) = 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  rw [hc, show (2 : F) = 0 from CharTwo.two_eq_zero, zero_add, inv_mul_cancel₀ hb]

private lemma op_smul_eq (a b : F) : MulOpposite.op a • b = a * b := by
  simp [mul_comm]

private lemma adjWedgeM_mulVec (u v w : Om6Idx → F) :
    wedgeM u v *ᵥ w = (v ⬝ᵥ w) • u + (u ⬝ᵥ w) • v := by
  funext i
  simp only [wedgeM, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.smul_apply,
    op_smul_eq]
  ring

private lemma dotProduct_adjGram_mulVec (c : F) (v w : Om6Idx → F) :
    v ⬝ᵥ (adjGram c *ᵥ w) = adjPolar c v w := by
  simp only [adjGram, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, adjWedgeM_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_sum, single_one_dotProduct, dotProduct_single_one,
    adjStdVec, adjPolar, Finset.sum_add_distrib, mul_add, smul_eq_mul]
  have e : (∑ x : Fin (3 - 1), w (.inr (.inl x)) * v (.inl x)) =
      ∑ x : Fin (3 - 1), v (.inl x) * w (.inr (.inl x)) :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [e]
  ring

private lemma dotProduct_stdVec_stdVec (A : Matrix Om6Idx Om6Idx F) (r s : Om6Idx) :
    adjStdVec r ⬝ᵥ (A *ᵥ adjStdVec s) = A r s := by
  simp only [adjStdVec, single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]

private lemma dotProduct_mulVec' (B : Matrix Om6Idx Om6Idx F) (v w : Om6Idx → F) :
    v ⬝ᵥ (B *ᵥ w) = (Bᵀ *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

private lemma adjPolar_mulVec' {b c : F} {A : Matrix Om6Idx Om6Idx F}
    (hiso : ∀ v, StatedQuadMinus 3 F b c (A *ᵥ v) = StatedQuadMinus 3 F b c v)
    (v w : Om6Idx → F) : adjPolar b (A *ᵥ v) (A *ᵥ w) = adjPolar b v w := by
  rw [adjPolar_eq_polar, adjPolar_eq_polar, quadraticPolar_eq_add, quadraticPolar_eq_add,
    ← Matrix.mulVec_add, hiso, hiso, hiso]

private lemma adjGram_conj {b c : F} {A : Matrix Om6Idx Om6Idx F}
    (hiso : ∀ v, StatedQuadMinus 3 F b c (A *ᵥ v) = StatedQuadMinus 3 F b c v) :
    Aᵀ * adjGram b * A = adjGram b := by
  ext r s
  rw [← dotProduct_stdVec_stdVec (Aᵀ * adjGram b * A) r s,
    ← dotProduct_stdVec_stdVec (adjGram b) r s, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec', Matrix.transpose_transpose, dotProduct_adjGram_mulVec,
    adjPolar_mulVec' hiso, dotProduct_adjGram_mulVec]

private lemma adjDotProduct_mulVec_self_eq_zero {X : Matrix Om6Idx Om6Idx F} (hX : Xᵀ = X)
    (hd : ∀ i, X i i = 0) (v : Om6Idx → F) : v ⬝ᵥ (X *ᵥ v) = 0 := by
  have hXs : ∀ i j, X j i = X i j := by
    intro i j
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hX j) i).symm
  have hsum : v ⬝ᵥ (X *ᵥ v) = ∑ p : Om6Idx × Om6Idx, v p.1 * (X p.1 p.2 * v p.2) := by
    rw [show v ⬝ᵥ (X *ᵥ v) = ∑ i, ∑ j, v i * (X i j * v j) from by
      simp only [dotProduct, Matrix.mulVec_apply, Matrix.row_apply, Finset.mul_sum]]
    rw [Fintype.sum_prod_type]
  rw [hsum]
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun p _ => Finset.mem_univ _)
    (fun p _ => rfl)
  · rintro ⟨i, j⟩ -; simp only [Prod.fst_swap, Prod.snd_swap, hXs]
    have h : v j * (X i j * v i) = v i * (X i j * v j) := by ring
    rw [h, CharTwo.add_self_eq_zero]
  · rintro ⟨i, j⟩ - hp h
    have hij : i = j := (congrArg Prod.fst h).symm
    subst hij
    exact hp (by simp [hd i])

private lemma trace_mul_eq_zero {D X : Matrix Om6Idx Om6Idx F} (hD : Dᵀ + D = 0) (hX : Xᵀ = X)
    (hd : ∀ i, X i i = 0) : (D * X).trace = 0 := by
  have hDs : ∀ i j, D i j + D j i = 0 := by
    intro i j
    have h := congrFun (congrFun hD i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Pi.zero_apply] at h
    rw [add_comm]
    exact h
  have hXs : ∀ i j, X j i = X i j := by
    intro i j
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hX j) i).symm
  have hsum : (D * X).trace = ∑ p : Om6Idx × Om6Idx, D p.1 p.2 * X p.1 p.2 := by
    rw [show (D * X).trace = ∑ i, ∑ j, D i j * X j i from by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hXs]
  rw [hsum]
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun p _ => Finset.mem_univ _)
    (fun p _ => rfl)
  · rintro ⟨i, j⟩ -
    simp only [Prod.fst_swap, Prod.snd_swap]
    calc D i j * X i j + D j i * X j i = D i j * X i j + D j i * X i j := by rw [hXs]
      _ = (D i j + D j i) * X i j := by ring
      _ = 0 := by rw [hDs]; simp
  · rintro ⟨i, j⟩ - hp h
    have hij : i = j := (congrArg Prod.fst h).symm
    subst hij
    exact hp (by simp [hd i])

theorem mem_adjOmega6_conj {b c : F} {A : Matrix Om6Idx Om6Idx F}
    (hiso : ∀ v, StatedQuadMinus 3 F b c (A *ᵥ v) = StatedQuadMinus 3 F b c v)
    {X : Matrix Om6Idx Om6Idx F} (hX : X ∈ adjOmega6 F b) :
    A * X * Aᵀ ∈ adjOmega6 F b := by
  obtain ⟨hXs, hXd, hXt⟩ := hX
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hXs,
      Matrix.mul_assoc]
  · intro i
    rw [← dotProduct_stdVec_stdVec (A * X * Aᵀ) i i, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, dotProduct_mulVec', adjDotProduct_mulVec_self_eq_zero hXs hXd]
  · show wedgeTrace b (A * X * Aᵀ) = 0
    set D := Aᵀ * adjTrace b * A - adjTrace b with hDdef
    have hD : Dᵀ + D = 0 := by
      have h1 : (adjTrace b)ᵀ + adjTrace b = adjGram b := by
        rw [add_comm, adjTrace_transpose_add]
      have h0 : Dᵀ + D =
          Aᵀ * ((adjTrace b)ᵀ + adjTrace b) * A - ((adjTrace b)ᵀ + adjTrace b) := by
        rw [hDdef, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
          Matrix.transpose_transpose]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel_nf
      rw [h0, h1, adjGram_conj hiso, sub_self]
    have htr : wedgeTrace b (A * X * Aᵀ) = (adjTrace b * X).trace + (D * X).trace := by
      rw [← trace_adjTrace_mul]
      have e1 : adjTrace b * (A * X * Aᵀ) = adjTrace b * A * X * Aᵀ := by
        simp only [Matrix.mul_assoc]
      rw [e1, Matrix.trace_mul_comm (adjTrace b * A * X) Aᵀ]
      have e2 : Aᵀ * (adjTrace b * A * X) = (Aᵀ * adjTrace b * A) * X := by
        simp only [Matrix.mul_assoc]
      rw [e2]
      have e3 : Aᵀ * adjTrace b * A = adjTrace b + D := by
        rw [hDdef]
        abel
      conv_lhs => rw [e3]
      rw [Matrix.add_mul, Matrix.trace_add]
    rw [htr, trace_mul_eq_zero hD hXs hXd, trace_adjTrace_mul, add_zero]
    exact hXt

private lemma wedgeTrace_sub (b : F) (X Y : Matrix Om6Idx Om6Idx F) :
    wedgeTrace b (X - Y) = wedgeTrace b X - wedgeTrace b Y := by
  simp only [wedgeTrace, Matrix.sub_apply, Finset.sum_sub_distrib]
  ring

private lemma adjGram_transpose (b : F) : (adjGram b)ᵀ = adjGram b := by
  rw [← adjTrace_transpose_add, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

private lemma adjPolar_std_inl (c : F) (w : Om6Idx → F) (i : Fin (3 - 1)) :
    adjPolar c (adjStdVec (.inl i)) w = w (.inr (.inl i)) := by
  simp [adjPolar, adjStdVec, Pi.single_apply, Finset.sum_ite_eq]

private lemma adjPolar_std_inr_inl (c : F) (w : Om6Idx → F) (i : Fin (3 - 1)) :
    adjPolar c (adjStdVec (.inr (.inl i))) w = w (.inl i) := by
  simp [adjPolar, adjStdVec, Pi.single_apply, Finset.sum_ite_eq]

private lemma adjPolar_std_inr_inr (c : F) (w : Om6Idx → F) (j : Fin 2) :
    adjPolar c (adjStdVec (.inr (.inr j))) w = c * w (.inr (.inr (Fin.rev j))) := by
  fin_cases j <;> simp [adjPolar, adjStdVec, Pi.single_apply, Finset.sum_ite_eq, Fin.rev]

private lemma adjGram_mulVec_apply (c : F) (w : Om6Idx → F) (r : Om6Idx) :
    (adjGram c *ᵥ w) r = adjPolar c (adjStdVec r) w := by
  rw [← single_one_dotProduct r (adjGram c *ᵥ w), dotProduct_adjGram_mulVec]
  rfl

private lemma adjGram_mulVec_adjGram (c c' : F) (h : c * c' = 1) (w : Om6Idx → F) :
    adjGram c *ᵥ (adjGram c' *ᵥ w) = w := by
  funext r
  rw [adjGram_mulVec_apply]
  rcases r with (i | i | j)
  · rw [adjPolar_std_inl, adjGram_mulVec_apply, adjPolar_std_inr_inl]
  · rw [adjPolar_std_inr_inl, adjGram_mulVec_apply, adjPolar_std_inl]
  · rw [adjPolar_std_inr_inr, adjGram_mulVec_apply, adjPolar_std_inr_inr, ← mul_assoc, h,
      one_mul, Fin.rev_rev]

private lemma adjGram_mulVec_adjBinv (b : F) (hb : b ≠ 0) (w : Om6Idx → F) :
    adjGram b *ᵥ (adjBinv b *ᵥ w) = w := by
  rw [adjBinv_eq_adjGram]
  exact adjGram_mulVec_adjGram b b⁻¹ (mul_inv_cancel₀ hb) w

private lemma adjBinv_mulVec_adjGram (b : F) (hb : b ≠ 0) (w : Om6Idx → F) :
    adjBinv b *ᵥ (adjGram b *ᵥ w) = w := by
  rw [adjBinv_eq_adjGram]
  exact adjGram_mulVec_adjGram b⁻¹ b (inv_mul_cancel₀ hb) w

private lemma adjBinv_conj {b c : F} (hb : b ≠ 0) {A B : Matrix Om6Idx Om6Idx F}
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hiso : ∀ v, StatedQuadMinus 3 F b c (A *ᵥ v) = StatedQuadMinus 3 F b c v) :
    A * adjBinv b * Aᵀ = adjBinv b := by
  have hinj : ∀ x y : Om6Idx → F, adjGram b *ᵥ x = adjGram b *ᵥ y → x = y := by
    intro x y hxy
    calc x = adjBinv b *ᵥ (adjGram b *ᵥ x) := (adjBinv_mulVec_adjGram b hb x).symm
      _ = adjBinv b *ᵥ (adjGram b *ᵥ y) := by rw [hxy]
      _ = y := adjBinv_mulVec_adjGram b hb y
  have h1 : Aᵀ * adjGram b = adjGram b * B := by
    calc Aᵀ * adjGram b = Aᵀ * adjGram b * (A * B) := by rw [hAB, mul_one]
      _ = Aᵀ * adjGram b * A * B := by simp only [Matrix.mul_assoc]
      _ = adjGram b * B := by rw [adjGram_conj hiso]
  have h2 : adjGram b * A = Bᵀ * adjGram b := by
    have h := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      adjGram_transpose] at h
  apply Matrix.mulVec_injective
  funext z
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine hinj (A *ᵥ (adjBinv b *ᵥ (Aᵀ *ᵥ z))) (adjBinv b *ᵥ z) ?_
  rw [adjGram_mulVec_adjBinv b hb]
  calc adjGram b *ᵥ (A *ᵥ (adjBinv b *ᵥ (Aᵀ *ᵥ z)))
      = (adjGram b * A) *ᵥ (adjBinv b *ᵥ (Aᵀ *ᵥ z)) := by rw [Matrix.mulVec_mulVec]
    _ = (Bᵀ * adjGram b) *ᵥ (adjBinv b *ᵥ (Aᵀ *ᵥ z)) := by rw [h2]
    _ = Bᵀ *ᵥ (adjGram b *ᵥ (adjBinv b *ᵥ (Aᵀ *ᵥ z))) := by rw [← Matrix.mulVec_mulVec]
    _ = Bᵀ *ᵥ (Aᵀ *ᵥ z) := by rw [adjGram_mulVec_adjBinv b hb]
    _ = (Bᵀ * Aᵀ) *ᵥ z := by rw [← Matrix.mulVec_mulVec]
    _ = ((A * B)ᵀ) *ᵥ z := by rw [Matrix.transpose_mul]
    _ = z := by rw [hAB, Matrix.transpose_one, Matrix.one_mulVec]

theorem mem_adjOmega6_adjWedge (b : F) (hb : b ≠ 0) (v w : Om6Idx → F) :
    wedgeM v w - adjPolar b v w • adjBinv b ∈ adjOmega6 F b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_smul, wedgeM_transpose, adjBinv_transpose]
  · intro i
    rw [Matrix.sub_apply, Matrix.smul_apply, wedgeM_diag, adjBinv_eq_adjGram, adjGram_diag,
      smul_eq_mul, mul_zero, sub_zero]
  · show wedgeTrace b (wedgeM v w - adjPolar b v w • adjBinv b) = 0
    rw [wedgeTrace_sub, wedgeTrace_smul, wedgeTrace_wedgeM, wedgeTrace_adjBinv b hb]
    ring

private lemma adjConj_of_mul_eq_one {A B : Matrix Om6Idx Om6Idx F} (hAB : A * B = 1)
    (hBA : B * A = 1) (X : Matrix Om6Idx Om6Idx F) : B * (A * X * Aᵀ) * Bᵀ = X := by
  calc B * (A * X * Aᵀ) * Bᵀ = (B * A) * X * (Aᵀ * Bᵀ) := by noncomm_ring
    _ = X := by
      rw [hBA, Matrix.one_mul, ← Matrix.transpose_mul, hBA, Matrix.transpose_one,
        Matrix.mul_one]

private lemma conj_wedgeM {A : Matrix Om6Idx Om6Idx F} (v w : Om6Idx → F) :
    A * wedgeM v w * Aᵀ = wedgeM (A *ᵥ v) (A *ᵥ w) := by
  simp only [wedgeM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose]

private lemma adjWedgeM_add_right (v w w' : Om6Idx → F) :
    wedgeM v (w + w') = wedgeM v w + wedgeM v w' := by
  ext i j
  simp only [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply, mul_add, add_mul]
  ring

private lemma adjPolar_second_add (b : F) (v w w' : Om6Idx → F) :
    adjPolar b v (w + w') = adjPolar b v w + adjPolar b v w' := by
  rw [← dotProduct_adjGram_mulVec, ← dotProduct_adjGram_mulVec, ← dotProduct_adjGram_mulVec,
    Matrix.mulVec_add, dotProduct_add]

private lemma adjPolar_swap (b : F) (v w : Om6Idx → F) : adjPolar b v w = adjPolar b w v := by
  simp only [adjPolar, add_comm]

private lemma adjWedgeM_comm (v w : Om6Idx → F) : wedgeM v w = wedgeM w v := by
  simp only [wedgeM, add_comm]

private lemma adjWedgeM_smul_left (c : F) (v w : Om6Idx → F) :
    wedgeM (c • v) w = c • wedgeM v w := by
  simp only [wedgeM, Pi.smul_apply, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_add]

private lemma adjPolar_first_smul (b : F) (c : F) (v w : Om6Idx → F) :
    adjPolar b (c • v) w = c * adjPolar b v w := by
  rw [← dotProduct_adjGram_mulVec, ← dotProduct_adjGram_mulVec, smul_dotProduct, smul_eq_mul]

private lemma adjPolar_second_smul (b : F) (c : F) (v w : Om6Idx → F) :
    adjPolar b v (c • w) = c * adjPolar b v w := by
  rw [← dotProduct_adjGram_mulVec, ← dotProduct_adjGram_mulVec, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

private lemma toAdd_ext {b : F} {x y : Multiplicative ↥(adjOmega6 F b)}
    (h : ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) =
      ((Multiplicative.toAdd y : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F)) : x = y := by
  have h' : Multiplicative.toAdd x = Multiplicative.toAdd y := Subtype.ext h
  calc x = Multiplicative.ofAdd (Multiplicative.toAdd x) := rfl
    _ = Multiplicative.ofAdd (Multiplicative.toAdd y) := by rw [h']
    _ = y := rfl

@[expose] noncomputable def adjAct (F : Type) [Field F] [CharP F 2] (b c : F) :
    ↥(omIsoGroup (StatedQuadMinus 3 F b c)) →* MulAut (Multiplicative ↥(adjOmega6 F b)) where
  toFun g :=
    { toFun := fun x => Multiplicative.ofAdd
        ⟨((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
            ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ,
          mem_adjOmega6_conj (fun v => g.2 v) (Multiplicative.toAdd x).2⟩
      invFun := fun x => Multiplicative.ofAdd
        ⟨((g⁻¹ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
            ((g⁻¹ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ,
          mem_adjOmega6_conj (fun v => (g⁻¹).2 v) (Multiplicative.toAdd x).2⟩
      left_inv := fun x => by
        have hAB : ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((g⁻¹ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hBA : ((g⁻¹ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        apply Multiplicative.ofAdd.injective
        apply Subtype.ext
        exact adjConj_of_mul_eq_one hAB hBA _
      right_inv := fun x => by
        have hAB : ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((g⁻¹ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hBA : ((g⁻¹ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        apply Multiplicative.ofAdd.injective
        apply Subtype.ext
        exact adjConj_of_mul_eq_one hBA hAB _
      map_mul' := fun x y => by
        refine toAdd_ext ?_
        show ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((Multiplicative.toAdd (x * y) : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
            ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ =
          ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
              ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
              ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ +
            ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
              ((Multiplicative.toAdd y : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
              ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ
        rw [show ((Multiplicative.toAdd (x * y) : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) =
            ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) +
            ((Multiplicative.toAdd y : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) from rfl]
        rw [Matrix.mul_add, Matrix.add_mul] }
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    refine toAdd_ext ?_
    simp
  map_mul' := fun g h => by
    refine MulEquiv.ext fun x => ?_
    refine toAdd_ext ?_
    show ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
          ((h : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
          ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
          (((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((h : GL Om6Idx F) : Matrix Om6Idx Om6Idx F))ᵀ =
      ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
          (((h : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
            ((h : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ) *
          ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ
    rw [Matrix.transpose_mul]
    noncomm_ring

private lemma adjAct_apply_aux {F : Type} [Field F] [CharP F 2] {b c : F}
    (g : ↥(omIsoGroup (StatedQuadMinus 3 F b c))) (x : Multiplicative ↥(adjOmega6 F b)) :
    ((Multiplicative.toAdd (adjAct F b c g x) : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) =
      ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
        ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
        ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ := rfl

theorem adjAct_apply {F : Type} [Field F] [CharP F 2] {b c : F}
    (g : ↥(omIsoGroup (StatedQuadMinus 3 F b c))) (x : Multiplicative ↥(adjOmega6 F b)) :
    ((Multiplicative.toAdd (adjAct F b c g x) : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) =
      ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
        ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
        ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ := adjAct_apply_aux g x

@[expose] noncomputable def adjWedge {F : Type} [Field F] [CharP F 2] (b : F) (v w : Om6Idx → F) :
    Multiplicative ↥(adjOmega6 F b) :=
  haveI := Classical.propDecidable (b = 0)
  if h : b = 0 then 1 else
    Multiplicative.ofAdd
      ⟨wedgeM v w - adjPolar b v w • adjBinv b, mem_adjOmega6_adjWedge b h v w⟩

lemma toAdd_adjWedge {b : F} (hb : b ≠ 0) (v w : Om6Idx → F) :
    ((Multiplicative.toAdd (adjWedge b v w) : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) =
      wedgeM v w - adjPolar b v w • adjBinv b := by
  rw [adjWedge, dif_neg hb]
  rfl

private lemma toAdd_adjWedge_mul {b : F} (hb : b ≠ 0) (v w w' : Om6Idx → F) :
    ((Multiplicative.toAdd (adjWedge b v w * adjWedge b v w') : ↥(adjOmega6 F b)) :
        Matrix Om6Idx Om6Idx F) =
      (wedgeM v w - adjPolar b v w • adjBinv b) +
        (wedgeM v w' - adjPolar b v w' • adjBinv b) := by
  rw [show Multiplicative.toAdd (adjWedge b v w * adjWedge b v w') =
      Multiplicative.toAdd (adjWedge b v w) + Multiplicative.toAdd (adjWedge b v w') from rfl,
    AddSubgroup.coe_add, toAdd_adjWedge hb, toAdd_adjWedge hb]

private lemma adjWedgeM_smul_right (c : F) (v w : Om6Idx → F) :
    wedgeM v (c • w) = c • wedgeM v w := by
  ext i j
  simp only [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem adjWedge_add_right {F : Type} [Field F] [CharP F 2] (b : F) (v w w' : Om6Idx → F) :
    adjWedge b v (w + w') = adjWedge b v w * adjWedge b v w' := by
  by_cases hb : b = 0
  · simp [adjWedge, hb]
  · refine toAdd_ext ?_
    rw [toAdd_adjWedge hb, toAdd_adjWedge_mul hb, adjWedgeM_add_right, adjPolar_second_add,
      add_smul]
    abel

theorem adjWedge_smul {F : Type} [Field F] [CharP F 2] (b : F) (s : F) (v w : Om6Idx → F) :
    adjWedge b (s • v) w = adjWedge b v (s • w) := by
  by_cases hb : b = 0
  · simp [adjWedge, hb]
  · refine toAdd_ext ?_
    rw [toAdd_adjWedge hb, toAdd_adjWedge hb]
    have h1 : wedgeM (s • v) w - adjPolar b (s • v) w • adjBinv b =
        s • (wedgeM v w - adjPolar b v w • adjBinv b) := by
      rw [adjWedgeM_smul_left, adjPolar_first_smul, smul_sub, smul_smul]
    have h2 : wedgeM v (s • w) - adjPolar b v (s • w) • adjBinv b =
        s • (wedgeM v w - adjPolar b v w • adjBinv b) := by
      rw [adjWedgeM_smul_right, adjPolar_second_smul, smul_sub, smul_smul]
    rw [h1, h2]

theorem adjWedge_comm {F : Type} [Field F] [CharP F 2] (b : F) (v w : Om6Idx → F) :
    adjWedge b v w = adjWedge b w v := by
  by_cases hb : b = 0
  · simp [adjWedge, hb]
  · refine toAdd_ext ?_
    rw [toAdd_adjWedge hb, toAdd_adjWedge hb, adjWedgeM_comm, adjPolar_swap]

theorem adjPolar_mulVec {F : Type} [Field F] [CharP F 2] {b c : F}
    (g : ↥(omIsoGroup (StatedQuadMinus 3 F b c))) (v w : Om6Idx → F) :
    adjPolar b (((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ v)
      (((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ w) = adjPolar b v w :=
  adjPolar_mulVec' (fun v => g.2 v) v w

theorem adjAct_adjWedge {F : Type} [Field F] [CharP F 2] {b c : F} (hb : b ≠ 0)
    (g : ↥(omIsoGroup (StatedQuadMinus 3 F b c))) (v w : Om6Idx → F) :
    adjAct F b c g (adjWedge b v w) =
      adjWedge b (((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ v)
        (((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ w) := by
  have hAB : ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
      ((g⁻¹ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : ((g⁻¹ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
      ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine toAdd_ext ?_
  rw [adjAct_apply, toAdd_adjWedge hb, toAdd_adjWedge hb, adjPolar_mulVec' (fun v => g.2 v),
    Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul, conj_wedgeM,
    adjBinv_conj hb hAB hBA (fun v => g.2 v)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
