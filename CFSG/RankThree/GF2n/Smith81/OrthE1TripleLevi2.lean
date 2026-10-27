module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleLevi
public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleGlue
public import CFSG.RankThree.GF2n.Smith81.OrthE1Sp4Levi

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

open CFSG.Open KFacts.Sp4TwistedLevi

section Sp4Basics

variable {K : Type} [Field K]

@[expose] def lv2m (g : ↥(StatedSp 2 K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

@[expose] def lv2J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem lv2J_def : (lv2J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
    Matrix.fromBlocks 0 1 (-1) 0 := rfl

theorem lv2_gram_expand (P Q R T : Matrix (Fin 2) (Fin 2) K) :
    (Matrix.fromBlocks P Q R T)ᵀ * lv2J * Matrix.fromBlocks P Q R T =
      Matrix.fromBlocks (Pᵀ * R - Rᵀ * P) (Pᵀ * T - Rᵀ * Q) (Qᵀ * R - Tᵀ * P)
        (Qᵀ * T - Tᵀ * Q) := by
  rw [lv2J_def, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.transpose_zero]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> abel

theorem lv2_gram_iff (P Q R T : Matrix (Fin 2) (Fin 2) K) :
    (Matrix.fromBlocks P Q R T)ᵀ * lv2J * Matrix.fromBlocks P Q R T = lv2J ↔
      (Pᵀ * R = Rᵀ * P ∧ Pᵀ * T - Rᵀ * Q = 1 ∧ Qᵀ * R - Tᵀ * P = -1 ∧ Qᵀ * T = Tᵀ * Q) := by
  rw [lv2_gram_expand, lv2J_def, Matrix.fromBlocks_inj]
  simp only [sub_eq_zero]

@[expose] def lv2Blk (h : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks (h 0 0 • (1 : Matrix (Fin 2) (Fin 2) K)) (h 0 1 • S0)
    (h 1 0 • S0) (h 1 1 • (1 : Matrix (Fin 2) (Fin 2) K))

theorem lv2Blk_one : lv2Blk (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [lv2Blk, Matrix.one_apply, Matrix.fromBlocks]

theorem lv2Blk_mul (A B : Matrix (Fin 2) (Fin 2) K) : lv2Blk (A * B) = lv2Blk A * lv2Blk B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [lv2Blk, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, S0,
      Matrix.one_apply] <;> ring

theorem lv2Blk_gram (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) :
    (lv2Blk A)ᵀ * lv2J * lv2Blk A = lv2J := by
  have h2 : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← hA, Matrix.det_fin_two]
  rw [lv2J_def]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [lv2Blk, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      S0, Matrix.one_apply, Matrix.fromBlocks_multiply] <;>
    first
    | ring1
    | linear_combination h2
    | linear_combination (-1 : K) * h2
    | linear_combination (2 : K) * h2
    | linear_combination (-2 : K) * h2

theorem lv2_inv_transpose [CharP K 2] (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) :
    (A⁻¹)ᵀ = S0 * A * S0 := by
  rw [Matrix.inv_def, hA, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S0, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, Matrix.vecMul, dotProduct,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]

theorem lv2Blk_comm_levi [CharP K 2] (h A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) :
    lv2Blk h * Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ = Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * lv2Blk h := by
  rw [lv2_inv_transpose A hA]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [lv2Blk, Matrix.fromBlocks_multiply, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, S0, Matrix.one_apply, Matrix.fromBlocks, Matrix.vecMul, dotProduct] <;>
    ring

theorem lv2Blk_mul_inv (h : Matrix.SpecialLinearGroup (Fin 2) K) :
    lv2Blk (h : Matrix (Fin 2) (Fin 2) K) * lv2Blk ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← lv2Blk_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, lv2Blk_one]

theorem lv2Blk_inv_mul (h : Matrix.SpecialLinearGroup (Fin 2) K) :
    lv2Blk ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      lv2Blk (h : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← lv2Blk_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, lv2Blk_one]

@[expose] def lv2ThetaGL (h : Matrix.SpecialLinearGroup (Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K :=
  Units.mk (lv2Blk (h : Matrix (Fin 2) (Fin 2) K))
    (lv2Blk ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (lv2Blk_mul_inv h) (lv2Blk_inv_mul h)

theorem lv2ThetaGL_mem (h : Matrix.SpecialLinearGroup (Fin 2) K) :
    lv2ThetaGL h ∈ StatedSp 2 K := by
  rw [StatedAPI.mem_statedSp_iff]
  exact lv2Blk_gram _ h.2

@[expose] def lv2Theta : Matrix.SpecialLinearGroup (Fin 2) K →* ↥(StatedSp 2 K) where
  toFun h := ⟨lv2ThetaGL h, lv2ThetaGL_mem h⟩
  map_one' := Subtype.ext (Units.ext lv2Blk_one)
  map_mul' h h' := Subtype.ext (Units.ext (by
    change lv2Blk ((h * h' : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      lv2Blk (h : Matrix (Fin 2) (Fin 2) K) * lv2Blk (h' : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, lv2Blk_mul]))

@[expose] def lv2Fa (K : Type) [Field K] : Subgroup ↥(StatedSp 2 K) := lv2Theta.range

theorem lv2m_theta (h : Matrix.SpecialLinearGroup (Fin 2) K) :
    lv2m (lv2Theta h) = lv2Blk (h : Matrix (Fin 2) (Fin 2) K) := rfl

theorem lv2m_levSp {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    lv2m (levSp A hA) = Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ := rfl

theorem lv2m_mul (g h : ↥(StatedSp 2 K)) : lv2m (g * h) = lv2m g * lv2m h := rfl

theorem lv2m_one : lv2m (1 : ↥(StatedSp 2 K)) = 1 := rfl

theorem lv2m_inv_mul (g : ↥(StatedSp 2 K)) : lv2m g⁻¹ * lv2m g = 1 := by
  rw [← lv2m_mul, inv_mul_cancel, lv2m_one]

theorem lv2Theta_mem_centralizer [CharP K 2] (h : Matrix.SpecialLinearGroup (Fin 2) K) :
    lv2Theta h ∈ Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)) := by
  refine mem_centralizer_of_levi fun B hB => ?_
  apply Subtype.ext
  apply Units.ext
  change lv2m (levSp B hB) * lv2m (lv2Theta h) = lv2m (lv2Theta h) * lv2m (levSp B hB)
  rw [lv2m_levSp, lv2m_theta]
  exact (lv2Blk_comm_levi _ B hB).symm

theorem lv2Fa_le_centralizer [CharP K 2] :
    lv2Fa K ≤ Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)) := by
  rintro _ ⟨h, rfl⟩
  exact lv2Theta_mem_centralizer h

@[expose] def lv2u1 : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]

@[expose] def lv2l1 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 1, 1]

theorem lv2u1_det : (lv2u1 : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [lv2u1, Matrix.det_fin_two]

theorem lv2l1_det : (lv2l1 : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [lv2l1, Matrix.det_fin_two]

theorem lv2u1_inv_T [CharP K 2] : ((lv2u1 : Matrix (Fin 2) (Fin 2) K)⁻¹)ᵀ = lv2l1 := by
  rw [lv2_inv_transpose _ lv2u1_det]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lv2u1, lv2l1, S0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem lv2l1_inv_T [CharP K 2] : ((lv2l1 : Matrix (Fin 2) (Fin 2) K)⁻¹)ᵀ = lv2u1 := by
  rw [lv2_inv_transpose _ lv2l1_det]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lv2u1, lv2l1, S0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem lv2_comm_diag (A B P Q R T : Matrix (Fin 2) (Fin 2) K)
    (h : Matrix.fromBlocks A 0 0 B * Matrix.fromBlocks P Q R T =
      Matrix.fromBlocks P Q R T * Matrix.fromBlocks A 0 0 B) :
    A * P = P * A ∧ A * Q = Q * B ∧ B * R = R * A ∧ B * T = T * B := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h
  simpa [Matrix.mul_zero, Matrix.zero_mul] using h

theorem lv2_blocks_of_comm (P Q R T : Matrix (Fin 2) (Fin 2) K)
    (h1 : lv2u1 * P = P * lv2u1) (h2 : lv2l1 * P = P * lv2l1) (h3 : lv2u1 * Q = Q * lv2l1)
    (h4 : lv2l1 * Q = Q * lv2u1) (h5 : lv2l1 * R = R * lv2u1) (h6 : lv2u1 * R = R * lv2l1)
    (h7 : lv2l1 * T = T * lv2l1) (h8 : lv2u1 * T = T * lv2u1) :
    P 1 0 = 0 ∧ P 0 1 = 0 ∧ P 1 1 = P 0 0 ∧ Q 0 0 = 0 ∧ Q 1 1 = 0 ∧ Q 1 0 = Q 0 1 ∧
      R 0 0 = 0 ∧ R 1 1 = 0 ∧ R 1 0 = R 0 1 ∧ T 1 0 = 0 ∧ T 0 1 = 0 ∧ T 1 1 = T 0 0 := by
  have ent : ∀ (M N : Matrix (Fin 2) (Fin 2) K), M = N → ∀ i j : Fin 2, M i j = N i j :=
    fun M N h i j => by rw [h]
  have a1 := ent _ _ h1 0 0
  have a2 := ent _ _ h1 0 1
  have b1 := ent _ _ h2 0 0
  have b2 := ent _ _ h2 1 0
  have c1 := ent _ _ h3 0 1
  have c2 := ent _ _ h3 1 1
  have d1 := ent _ _ h4 0 1
  have d2 := ent _ _ h4 1 1
  have f1 := ent _ _ h5 0 1
  have f2 := ent _ _ h5 1 1
  have g1 := ent _ _ h6 0 1
  have g2 := ent _ _ h6 0 0
  have k1 := ent _ _ h7 0 0
  have k2 := ent _ _ h7 0 1
  have l1 := ent _ _ h8 0 0
  have l2 := ent _ _ h8 0 1
  simp only [lv2u1, lv2l1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
    at a1 a2 b1 b2 c1 c2 d1 d2 f1 f2 g1 g2 k1 k2 l1 l2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination a1
  · linear_combination -b1
  · linear_combination a2
  · linear_combination -d1
  · linear_combination c1
  · linear_combination -d2
  · linear_combination -f1
  · linear_combination g1
  · linear_combination -f2
  · linear_combination l1
  · linear_combination -k1
  · linear_combination l2

theorem lv2_fromBlocks_eq_blk (P Q R T : Matrix (Fin 2) (Fin 2) K) (h10 : P 1 0 = 0)
    (h01 : P 0 1 = 0) (h11 : P 1 1 = P 0 0) (hq00 : Q 0 0 = 0) (hq11 : Q 1 1 = 0)
    (hqs : Q 1 0 = Q 0 1) (hr00 : R 0 0 = 0) (hr11 : R 1 1 = 0) (hrs : R 1 0 = R 0 1)
    (ht10 : T 1 0 = 0) (ht01 : T 0 1 = 0) (ht11 : T 1 1 = T 0 0) :
    Matrix.fromBlocks P Q R T = lv2Blk !![P 0 0, Q 0 1; R 0 1, T 0 0] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [lv2Blk, S0, Matrix.one_apply, h10, h01, h11, hq00, hq11, hqs, hr00, hr11, hrs, ht10,
      ht01, ht11]

theorem lv2_centralizer_blocks (g : ↥(StatedSp 2 K)) [CharP K 2]
    (hg : g ∈ Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K))) :
    ∃ P Q R T : Matrix (Fin 2) (Fin 2) K, lv2m g = Matrix.fromBlocks P Q R T ∧
      P 1 0 = 0 ∧ P 0 1 = 0 ∧ P 1 1 = P 0 0 ∧ Q 0 0 = 0 ∧ Q 1 1 = 0 ∧ Q 1 0 = Q 0 1 ∧
      R 0 0 = 0 ∧ R 1 1 = 0 ∧ R 1 0 = R 0 1 ∧ T 1 0 = 0 ∧ T 0 1 = 0 ∧ T 1 1 = T 0 0 ∧
      P 0 0 * T 0 0 - Q 0 1 * R 0 1 = 1 := by
  have hu : levSp lv2u1 lv2u1_det ∈ leviSL2 K := levSp_mem_levi _
  have hl : levSp lv2l1 lv2l1_det ∈ leviSL2 K := levSp_mem_levi _
  have cu := congrArg lv2m (Subgroup.mem_centralizer_iff.mp hg _ hu)
  have cl := congrArg lv2m (Subgroup.mem_centralizer_iff.mp hg _ hl)
  rw [lv2m_mul, lv2m_mul, lv2m_levSp, lv2u1_inv_T] at cu
  rw [lv2m_mul, lv2m_mul, lv2m_levSp, lv2l1_inv_T] at cl
  have hgram : (lv2m g)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * lv2m g =
      Matrix.fromBlocks 0 1 (-1) 0 := StatedAPI.mem_statedSp_iff.mp g.2
  have hM0 := (Matrix.fromBlocks_toBlocks (lv2m g)).symm
  generalize (lv2m g).toBlocks₁₁ = P at hM0
  generalize (lv2m g).toBlocks₁₂ = Q at hM0
  generalize (lv2m g).toBlocks₂₁ = R at hM0
  generalize (lv2m g).toBlocks₂₂ = T at hM0
  have hM : lv2m g = Matrix.fromBlocks P Q R T := hM0
  rw [hM] at cu cl hgram
  obtain ⟨c1, c2, c3, c4⟩ := lv2_comm_diag _ _ _ _ _ _ cu
  obtain ⟨d1, d2, d3, d4⟩ := lv2_comm_diag _ _ _ _ _ _ cl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ :=
    lv2_blocks_of_comm P Q R T c1 d1 c2 d2 c3 d3 c4 d4
  obtain ⟨g1, g2, -, -⟩ := (lv2_gram_iff P Q R T).mp hgram
  refine ⟨P, Q, R, T, hM, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, ?_⟩
  have h00 := congrFun (congrFun g2 0) 0
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne, Fin.zero_eta, Fin.isValue] at h00
  simp only [e1, e10, e7, e4, e9, e6] at h00
  linear_combination h00

theorem lv2_centralizer_le_Fa [CharP K 2] :
    Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)) ≤ lv2Fa K := by
  intro g hg
  obtain ⟨P, Q, R, T, hM, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hdet0⟩ :=
    lv2_centralizer_blocks g hg
  have hdet : (!![P 0 0, Q 0 1; R 0 1, T 0 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two]
    simpa using hdet0
  have hML : lv2m g = lv2Blk !![P 0 0, Q 0 1; R 0 1, T 0 0] := by
    rw [hM]
    exact lv2_fromBlocks_eq_blk P Q R T e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  refine MonoidHom.mem_range.mpr ⟨⟨_, hdet⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  exact (lv2m_theta _).trans hML.symm

theorem lv2Fa_eq_centralizer [CharP K 2] : lv2Fa K = Subgroup.centralizer
    (leviSL2 K : Set ↥(StatedSp 2 K)) :=
  le_antisymm lv2Fa_le_centralizer lv2_centralizer_le_Fa

end Sp4Basics

section Roots

variable {K : Type} [Field K]

@[expose] def lv2low (μ : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 (μ • S0) (1 : Matrix (Fin 2) (Fin 2) K)

theorem lv2low_mul (μ ν : K) : lv2low μ * lv2low ν = lv2low (μ + ν) := by
  unfold lv2low
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    add_smul]

theorem lv2low_zero : lv2low (0 : K) = 1 := by
  unfold lv2low
  simp

theorem lv2low_mul_neg (μ : K) : lv2low μ * lv2low (-μ) = 1 := by
  rw [lv2low_mul, add_neg_cancel, lv2low_zero]

@[expose] def lv2up (μ : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  uS (μ • (S0 : Matrix (Fin 2) (Fin 2) K))

theorem lv2up_mul [CharP K 2] (μ ν : K) : lv2up μ * lv2up ν = lv2up (μ + ν) := by
  unfold lv2up
  rw [uS_mul, add_smul]

theorem lv2up_zero [CharP K 2] : lv2up (0 : K) = 1 := by
  unfold lv2up
  rw [zero_smul, uS_zero]

@[expose] def lv2N (K : Type) [Field K] [CharP K 2] : Subgroup ↥(StatedSp 2 K) where
  carrier := {g | ∃ μ : K, lv2m g = lv2up μ}
  one_mem' := ⟨0, by
    change (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = lv2up 0
    rw [lv2up_zero]⟩
  mul_mem' := by
    rintro g h ⟨μ, hμ⟩ ⟨ν, hν⟩
    exact ⟨μ + ν, by rw [lv2m_mul, hμ, hν, lv2up_mul]⟩
  inv_mem' := by
    rintro g ⟨μ, hμ⟩
    refine ⟨-μ, ?_⟩
    calc lv2m g⁻¹ = lv2m g⁻¹ * (lv2up μ * lv2up (-μ)) := by
          rw [lv2up_mul, add_neg_cancel, lv2up_zero, mul_one]
      _ = lv2m g⁻¹ * lv2m g * lv2up (-μ) := by rw [hμ, mul_assoc]
      _ = lv2up (-μ) := by rw [lv2m_inv_mul, one_mul]

@[expose] def lv2Nm (K : Type) [Field K] : Subgroup ↥(StatedSp 2 K) where
  carrier := {g | ∃ μ : K, lv2m g = lv2low μ}
  one_mem' := ⟨0, by
    change (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = lv2low 0
    rw [lv2low_zero]⟩
  mul_mem' := by
    rintro g h ⟨μ, hμ⟩ ⟨ν, hν⟩
    exact ⟨μ + ν, by rw [lv2m_mul, hμ, hν, lv2low_mul]⟩
  inv_mem' := by
    rintro g ⟨μ, hμ⟩
    refine ⟨-μ, ?_⟩
    calc lv2m g⁻¹ = lv2m g⁻¹ * (lv2low μ * lv2low (-μ)) := by rw [lv2low_mul_neg, mul_one]
      _ = lv2m g⁻¹ * lv2m g * lv2low (-μ) := by rw [hμ, mul_assoc]
      _ = lv2low (-μ) := by rw [lv2m_inv_mul, one_mul]

theorem lv2_S0_transpose : (S0 : Matrix (Fin 2) (Fin 2) K)ᵀ = S0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S0]

theorem lv2low_gram (μ : K) : (lv2low μ)ᵀ * lv2J * lv2low μ = lv2J := by
  unfold lv2low
  rw [lv2_gram_iff]
  simp [Matrix.transpose_smul, lv2_S0_transpose]

theorem lv2up_gram [CharP K 2] (μ : K) : (lv2up μ)ᵀ * lv2J * lv2up μ = lv2J := by
  unfold lv2up uS
  rw [lv2_gram_iff]
  simp [Matrix.transpose_smul, lv2_S0_transpose]

@[expose] def lv2upE [CharP K 2] (μ : K) : ↥(StatedSp 2 K) :=
  ⟨Units.mk (lv2up μ) (lv2up (-μ)) (by rw [lv2up_mul, add_neg_cancel, lv2up_zero])
    (by rw [lv2up_mul, neg_add_cancel, lv2up_zero]),
    by rw [StatedAPI.mem_statedSp_iff]; exact lv2up_gram μ⟩

@[expose] def lv2lowE (μ : K) : ↥(StatedSp 2 K) :=
  ⟨Units.mk (lv2low μ) (lv2low (-μ)) (by rw [lv2low_mul, add_neg_cancel, lv2low_zero])
    (by rw [lv2low_mul, neg_add_cancel, lv2low_zero]),
    by rw [StatedAPI.mem_statedSp_iff]; exact lv2low_gram μ⟩

theorem lv2m_upE [CharP K 2] (μ : K) : lv2m (lv2upE μ) = lv2up μ := rfl

theorem lv2m_lowE (μ : K) : lv2m (lv2lowE μ) = lv2low μ := rfl

theorem lv2N_card [CharP K 2] : Nat.card (lv2N K) = Nat.card K := by
  symm
  refine Nat.card_eq_of_bijective (fun μ : K => (⟨lv2upE μ, ⟨μ, lv2m_upE μ⟩⟩ : lv2N K)) ⟨?_, ?_⟩
  · intro μ ν h
    have h1 : lv2up μ = lv2up ν := congrArg (fun x : lv2N K => lv2m (x : ↥(StatedSp 2 K))) h
    have h2 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 1)
    simpa [lv2up, uS, S0] using h2
  · rintro ⟨g, μ, hμ⟩
    refine ⟨μ, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
    exact hμ.symm

theorem lv2Nm_card : Nat.card (lv2Nm K) = Nat.card K := by
  symm
  refine Nat.card_eq_of_bijective (fun μ : K => (⟨lv2lowE μ, ⟨μ, lv2m_lowE μ⟩⟩ : lv2Nm K)) ⟨?_, ?_⟩
  · intro μ ν h
    have h1 : lv2low μ = lv2low ν := congrArg (fun x : lv2Nm K => lv2m (x : ↥(StatedSp 2 K))) h
    have h2 := congrFun (congrFun h1 (Sum.inr 0)) (Sum.inl 1)
    simpa [lv2low, S0] using h2
  · rintro ⟨g, μ, hμ⟩
    refine ⟨μ, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
    exact hμ.symm

theorem lv2Blk_unipSL (s : K) : lv2Blk (unipSL s : Matrix (Fin 2) (Fin 2) K) = lv2up s := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [lv2Blk, lv2up, uS, unipSL_apply, S0, Matrix.one_apply]

theorem lv2Blk_lowSL [CharP K 2] (c : K) :
    lv2Blk (lowSL c : Matrix (Fin 2) (Fin 2) K) = lv2low c := by
  rw [lowSL_apply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [lv2Blk, lv2low, S0, Matrix.one_apply]

theorem lv2Theta_unipSL [CharP K 2] (s : K) : lv2Theta (unipSL s) = lv2upE s :=
  Subtype.ext (Units.ext (lv2Blk_unipSL s))

theorem lv2Theta_lowSL [CharP K 2] (c : K) : lv2Theta (lowSL c) = lv2lowE c :=
  Subtype.ext (Units.ext (lv2Blk_lowSL c))

theorem lv2_SL_fact_of_ne [CharP K 2] (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    g = unipSL (((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      lowSL ((g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      unipSL (((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, unipSL_apply,
    lowSL_apply, unipSL_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;>
    first
    | ring1
    | linear_combination hdet
    | linear_combination (-1 : K) * hdet
    | linear_combination (2 : K) * hdet
    | linear_combination (-2 : K) * hdet

theorem lv2_lowSL_mul_neg [CharP K 2] (μ : K) : lowSL μ * lowSL (-μ) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, lowSL_apply, lowSL_apply,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lv2Theta_mem_of_roots [CharP K 2] (𝔄' : Subgroup ↥(StatedSp 2 K))
    (hN : ∀ μ : K, lv2upE μ ∈ 𝔄') (hNm : ∀ μ : K, lv2lowE μ ∈ 𝔄')
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : lv2Theta g ∈ 𝔄' := by
  have key : ∀ x : Matrix.SpecialLinearGroup (Fin 2) K,
      (x : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 → lv2Theta x ∈ 𝔄' := by
    intro x hx
    rw [lv2_SL_fact_of_ne x hx]
    simp only [map_mul, lv2Theta_unipSL, lv2Theta_lowSL]
    exact mul_mem (mul_mem (hN _) (hNm _)) (hN _)
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
      have := g.2
      rw [Matrix.det_fin_two] at this
      exact this
    have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
      intro h0
      rw [hc, h0] at hdet
      simp at hdet
    have hg1 : ((g * lowSL 1 : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, lowSL_apply]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, h11]
    have e : g = (g * lowSL 1) * lowSL (-1) := by
      rw [mul_assoc, lv2_lowSL_mul_neg, mul_one]
    rw [e, map_mul, lv2Theta_lowSL]
    exact mul_mem (key _ hg1) (hNm _)
  · exact key g hc

end Roots

section Vectors

variable {K : Type} [Field K]

theorem lv2_mulVec_dot {n : Type} [Fintype n] (M : Matrix n n K) (v x : n → K) :
    (M *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (Mᵀ *ᵥ x) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem lv2_sympPair_mul (g : ↥(StatedSp 2 K)) (v w : Fin 2 ⊕ Fin 2 → K) :
    sympPair 2 K (lv2m g *ᵥ v) (lv2m g *ᵥ w) = sympPair 2 K v w := by
  have h : (lv2m g)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * lv2m g =
      Matrix.fromBlocks 0 1 (-1) 0 := StatedAPI.mem_statedSp_iff.mp g.2
  unfold sympPair
  rw [lv2_mulVec_dot, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem lv2_sympPair_elim (x y x' y' : Fin 2 → K) :
    sympPair 2 K (Sum.elim x y) (Sum.elim x' y') = x ⬝ᵥ y' - y ⬝ᵥ x' := by
  unfold sympPair
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks]
  ring

@[expose] def lv2Alt (g : ↥(StatedSp 2 K)) : Prop :=
  ∀ v : Fin 2 ⊕ Fin 2 → K, sympPair 2 K v (lv2m g *ᵥ v) = 0

theorem lv2Alt_conj (x g : ↥(StatedSp 2 K)) (hg : lv2Alt g) : lv2Alt (x * g * x⁻¹) := by
  intro v
  obtain ⟨u, rfl⟩ : ∃ u, v = lv2m x *ᵥ u :=
    ⟨lv2m x⁻¹ *ᵥ v, by
      rw [Matrix.mulVec_mulVec, ← lv2m_mul, mul_inv_cancel, lv2m_one, Matrix.one_mulVec]⟩
  have hgv : lv2m (x * g * x⁻¹) *ᵥ (lv2m x *ᵥ u) = lv2m x *ᵥ (lv2m g *ᵥ u) := by
    rw [lv2m_mul, lv2m_mul]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, lv2m_inv_mul, Matrix.mul_one]
  rw [hgv, lv2_sympPair_mul]
  exact hg u

theorem lv2up_alt [CharP K 2] (μ : K) (v : Fin 2 ⊕ Fin 2 → K) :
    sympPair 2 K v (lv2up μ *ᵥ v) = 0 := by
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin 2 → K, v = Sum.elim x y :=
    ⟨fun i => v (Sum.inl i), fun i => v (Sum.inr i), by
      funext i; rcases i with i | i <;> rfl⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hw : lv2up μ *ᵥ Sum.elim x y =
      Sum.elim (x + μ • (S0 : Matrix (Fin 2) (Fin 2) K) *ᵥ y) y := by
    unfold lv2up uS
    rw [Matrix.fromBlocks_mulVec]
    funext i
    rcases i with i | i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, S0, mul_add, Matrix.smul_apply]
  rw [hw, lv2_sympPair_elim]
  simp only [dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Matrix.mulVec, S0,
    smul_eq_mul]
  simp
  linear_combination (-(μ * y 0 * y 1)) * h2

theorem lv2_block_lower [CharP K 2] (g : ↥(StatedSp 2 K))
    (hfix : ∀ z : Fin 2 → K, lv2m g *ᵥ Sum.elim (0 : Fin 2 → K) z = Sum.elim (0 : Fin 2 → K) z)
    (hA : lv2Alt g) : ∃ μ : K, lv2m g = lv2low μ := by
  have hgram : (lv2m g)ᵀ * lv2J * lv2m g = lv2J := StatedAPI.mem_statedSp_iff.mp g.2
  have hA' := hA
  unfold lv2Alt at hA'
  obtain ⟨P, Q, R, T, hM⟩ : ∃ P Q R T : Matrix (Fin 2) (Fin 2) K,
      lv2m g = Matrix.fromBlocks P Q R T := by
    refine ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks (lv2m g)).symm⟩
  rw [hM] at hfix hA' hgram
  have hQ : Q = 0 := by
    ext i j
    have := congrFun (hfix (Pi.single j 1)) (Sum.inl i)
    simpa [Matrix.fromBlocks_mulVec, Matrix.mulVec_single_one] using this
  have hT : T = 1 := by
    ext i j
    have := congrFun (hfix (Pi.single j 1)) (Sum.inr i)
    simpa [Matrix.fromBlocks_mulVec, Matrix.mulVec_single_one, Pi.single_apply,
      Matrix.one_apply] using this
  subst hQ hT
  have hg := (lv2_gram_iff P 0 R 1).mp hgram
  have hPt : Pᵀ = 1 := by simpa using hg.2.1
  have hP : P = 1 := Matrix.transpose_eq_one.mp hPt
  subst hP
  have hsym : Rᵀ = R := by simpa using hg.1.symm
  have hR00 : R 0 0 = 0 := by
    have := hA' (Sum.elim (Pi.single 0 1) 0)
    rw [Matrix.fromBlocks_mulVec, lv2_sympPair_elim] at this
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] using this
  have hR11 : R 1 1 = 0 := by
    have := hA' (Sum.elim (Pi.single 1 1) 0)
    rw [Matrix.fromBlocks_mulVec, lv2_sympPair_elim] at this
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] using this
  have hR10 : R 1 0 = R 0 1 := by
    have := congrFun (congrFun hsym 0) 1
    simpa using this
  refine ⟨R 0 1, ?_⟩
  rw [hM]
  unfold lv2low
  set c := R 0 1 with hc
  have hRS : R = c • (S0 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S0, hc, hR10, hR00, hR11]
  rw [hRS]

theorem lv2m_pow (g : ↥(StatedSp 2 K)) (k : ℕ) : lv2m (g ^ k) = (lv2m g) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, lv2m_one]
  | succ k ih => rw [pow_succ, pow_succ, lv2m_mul, ih]

@[expose] def lv2K (e : Fin 2 ⊕ Fin 2 → K) : Subgroup ↥(StatedSp 2 K) where
  carrier := {g | lv2m g *ᵥ e = e ∧ ∀ v, sympPair 2 K e v = 0 → ∃ c : K, lv2m g *ᵥ v = v + c • e}
  one_mem' := ⟨by rw [lv2m_one, Matrix.one_mulVec], fun v _ => ⟨0, by
    rw [lv2m_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro g h ⟨hge, hgv⟩ ⟨hhe, hhv⟩
    refine ⟨?_, fun v hv => ?_⟩
    · rw [lv2m_mul, ← Matrix.mulVec_mulVec, hhe, hge]
    · obtain ⟨c, hc⟩ := hhv v hv
      obtain ⟨d, hd⟩ := hgv v hv
      refine ⟨d + c, ?_⟩
      rw [lv2m_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_add, Matrix.mulVec_smul, hge,
        hd, add_smul, add_assoc]
  inv_mem' := by
    rintro g ⟨hge, hgv⟩
    have hinv : lv2m g⁻¹ *ᵥ e = e := by
      have h1 : lv2m g⁻¹ *ᵥ (lv2m g *ᵥ e) = e := by
        rw [Matrix.mulVec_mulVec, lv2m_inv_mul, Matrix.one_mulVec]
      rwa [hge] at h1
    refine ⟨hinv, fun v hv => ?_⟩
    obtain ⟨d, hd⟩ := hgv v hv
    have h1 : lv2m g⁻¹ *ᵥ (lv2m g *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, lv2m_inv_mul, Matrix.one_mulVec]
    rw [hd, Matrix.mulVec_add, Matrix.mulVec_smul, hinv] at h1
    refine ⟨-d, ?_⟩
    rw [neg_smul, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq h1

theorem lv2_sympPair_sub_right (e a b : Fin 2 ⊕ Fin 2 → K) :
    sympPair 2 K e (a - b) = sympPair 2 K e a - sympPair 2 K e b := by
  unfold sympPair
  rw [Matrix.mulVec_sub, dotProduct_sub]

theorem lv2K_pow_four [CharP K 2] (e : Fin 2 ⊕ Fin 2 → K) (g : ↥(StatedSp 2 K)) (hg : g ∈ lv2K e) :
    g ^ 4 = 1 := by
  obtain ⟨hge, hgv⟩ := hg
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := lv2m g - 1 with hA
  have hM : lv2m g = 1 + A := by rw [hA]; abel
  have hsym : ∀ v, sympPair 2 K e (A *ᵥ v) = 0 := by
    intro v
    have h1 : sympPair 2 K e (lv2m g *ᵥ v) = sympPair 2 K e v := by
      have := lv2_sympPair_mul g e v
      rwa [hge] at this
    have h2' : A *ᵥ v = lv2m g *ᵥ v - v := by rw [hA, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [h2', lv2_sympPair_sub_right, h1, sub_self]
  have hAe : ∀ v, sympPair 2 K e v = 0 → ∃ c : K, A *ᵥ v = c • e := by
    intro v hv
    obtain ⟨c, hc⟩ := hgv v hv
    refine ⟨c, ?_⟩
    rw [hA, Matrix.sub_mulVec, Matrix.one_mulVec, hc, add_sub_cancel_left]
  have hAe0 : A *ᵥ e = 0 := by
    rw [hA, Matrix.sub_mulVec, Matrix.one_mulVec, hge, sub_self]
  have hA3 : A * A * A = 0 := by
    ext i j
    have hv : (A * A * A) *ᵥ Pi.single j 1 = 0 := by
      have hw : ∀ w : Fin 2 ⊕ Fin 2 → K, A *ᵥ (A *ᵥ (A *ᵥ w)) = 0 := by
        intro w
        obtain ⟨c, hc⟩ := hAe (A *ᵥ w) (hsym w)
        rw [hc, Matrix.mulVec_smul, hAe0, smul_zero]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hw _
    have := congrFun hv i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  have hAA : A + A = 0 := by
    rw [← two_smul K A, h2, zero_smul]
  have hsq : (1 + A) * (1 + A) = 1 + A * A := by
    have : (1 + A) * (1 + A) = 1 + (A + A) + A * A := by noncomm_ring
    rw [this, hAA, add_zero]
  have h4 : (1 + A) ^ 4 = 1 := by
    have e1 : (1 + A) ^ 4 = (1 + A * A) * (1 + A * A) := by
      rw [← hsq]
      noncomm_ring
    rw [e1]
    have h' : (1 + A * A) * (1 + A * A) = 1 + (A * A + A * A) + A * (A * A * A) := by
      noncomm_ring
    rw [h', ← add_mul, hAA, zero_mul, hA3, mul_zero, add_zero, add_zero]
  apply Subtype.ext
  apply Units.ext
  show lv2m (g ^ 4) = lv2m 1
  rw [lv2m_pow, lv2m_one, hM]
  exact h4

theorem lv2_perp_line [CharP K 2] (a y : Fin 2 → K) (ha : a ≠ 0) (hay : a ⬝ᵥ y = 0) :
    ∃ c : K, (S0 : Matrix (Fin 2) (Fin 2) K) *ᵥ y = c • a := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [dotProduct, Fin.sum_univ_two] at hay
  by_cases h1 : a 1 = 0
  · have h0 : a 0 ≠ 0 := by
      intro h0
      apply ha
      funext i
      fin_cases i <;> simp [h0, h1]
    have hy0 : y 0 = 0 := by
      rw [h1, zero_mul, add_zero] at hay
      exact (mul_eq_zero.mp hay).resolve_left h0
    refine ⟨y 1 / a 0, ?_⟩
    funext i
    fin_cases i
    · simp [S0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hy0, h1]
      field_simp
    · simp [S0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hy0, h1]
  · refine ⟨y 0 / a 1, ?_⟩
    funext i
    fin_cases i
    · simp [S0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      linear_combination hay + (-(y 0 * a 0)) * h2
    · simp [S0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp

theorem lv2up_fix [CharP K 2] (μ : K) (x : Fin 2 → K) :
    lv2up μ *ᵥ Sum.elim x 0 = Sum.elim x 0 := by
  unfold lv2up uS
  rw [Matrix.fromBlocks_mulVec]
  funext i
  rcases i with i | i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lv2_N_le_K [CharP K 2] (a : Fin 2 → K) (ha : a ≠ 0) (n : ↥(StatedSp 2 K))
    (hn : n ∈ lv2N K) : n ∈ lv2K (Sum.elim a 0) := by
  obtain ⟨μ, hμ⟩ := hn
  refine ⟨by rw [hμ, lv2up_fix], fun v hv => ?_⟩
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin 2 → K, v = Sum.elim x y :=
    ⟨fun i => v (Sum.inl i), fun i => v (Sum.inr i), by
      funext i; rcases i with i | i <;> rfl⟩
  rw [lv2_sympPair_elim] at hv
  simp only [dotProduct_zero, zero_dotProduct, sub_zero] at hv
  obtain ⟨c, hc⟩ := lv2_perp_line a y ha hv
  refine ⟨μ * c, ?_⟩
  have hc0 : y 1 = c * a 0 := by
    simpa [S0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 0
  have hc1 : y 0 = c * a 1 := by
    simpa [S0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 1
  rw [hμ]
  unfold lv2up uS
  rw [Matrix.fromBlocks_mulVec]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, S0, hc0, hc1, smul_eq_mul,
      Matrix.vecHead, Matrix.vecTail] <;> ring

theorem lv2_conj_N_mem_K [CharP K 2] (W : ↥(StatedSp 2 K)) (c a : Fin 2 → K) (hc : c ≠ 0)
    (hWc : lv2m W *ᵥ Sum.elim c 0 = Sum.elim a 0) (n : ↥(StatedSp 2 K)) (hn : n ∈ lv2N K) :
    W * n * W⁻¹ ∈ lv2K (Sum.elim a 0) := by
  have hn' := lv2_N_le_K c hc n hn
  have h1 : lv2m W⁻¹ *ᵥ (lv2m W *ᵥ Sum.elim c 0) = Sum.elim c 0 := by
    rw [Matrix.mulVec_mulVec, lv2m_inv_mul, Matrix.one_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · rw [← hWc]
    simp only [lv2m_mul, ← Matrix.mulVec_mulVec]
    rw [h1, hn'.1]
  · set w := lv2m W⁻¹ *ᵥ v with hw
    have hvw : v = lv2m W *ᵥ w := by
      rw [hw, Matrix.mulVec_mulVec, ← lv2m_mul, mul_inv_cancel, lv2m_one, Matrix.one_mulVec]
    have hwc : sympPair 2 K (Sum.elim c 0) w = 0 := by
      have h2 := lv2_sympPair_mul W (Sum.elim c 0) w
      rw [hWc, ← hvw, hv] at h2
      exact h2.symm
    obtain ⟨d, hd⟩ := hn'.2 w hwc
    refine ⟨d, ?_⟩
    simp only [lv2m_mul, ← Matrix.mulVec_mulVec]
    rw [← hw, hd, Matrix.mulVec_add, Matrix.mulVec_smul, hWc, ← hvw]

theorem lv2_card_dvd_le {d q m : ℕ} (hq2 : 2 ∣ q) (hq4 : 4 ≤ q) (hd : d ∣ q * (q ^ 2 - 1))
    (hpow : d ∣ 2 ^ m) : d ≤ q := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow
  have hodd : Odd (q ^ 2 - 1) := by
    obtain ⟨k, rfl⟩ := hq2
    have hk : 2 ≤ k := by omega
    have hk2 : 4 ≤ k ^ 2 := by nlinarith
    have e : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    rw [e]
    exact Nat.odd_iff.mpr (by omega)
  have hcop : Nat.Coprime (2 ^ j) (q ^ 2 - 1) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  have hdiv : 2 ^ j ∣ q := hcop.dvd_of_dvd_mul_right hd
  exact Nat.le_of_dvd (by omega) hdiv

theorem lv2_eq_of_two_group {G : Type*} [Group G] [Finite G] (T H N : Subgroup G)
    (hNH : N ≤ H) (hHT : H ≤ T) (hexp : ∀ g ∈ H, g ^ 4 = 1) (q : ℕ) (hq2 : 2 ∣ q)
    (hq4 : 4 ≤ q) (hT : Nat.card T = q * (q ^ 2 - 1)) (hN : Nat.card N = q) : N = H := by
  have hP : IsPGroup 2 H := fun g => ⟨2, by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hexp _ g.2⟩
  obtain ⟨m, hm⟩ := isPGroup_iff_card_dvd_pow.mp hP
  have hd1 : Nat.card H ∣ Nat.card T := Subgroup.card_dvd_of_le hHT
  have hle : Nat.card H ≤ q := lv2_card_dvd_le hq2 hq4 (by rw [← hT]; exact hd1) hm
  exact Subgroup.eq_of_le_of_card_ge hNH (by omega)

theorem lv2_two_dvd_card [Finite K] [CharP K 2] : 2 ∣ Nat.card K := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hcard]
  exact dvd_pow_self 2 (PNat.ne_zero n)

theorem lv2_step2 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (𝔄 : Subgroup ↥(StatedSp 2 K))
    (hN : lv2N K ≤ 𝔄) (hcard : Nat.card 𝔄 = Nat.card K * (Nat.card K ^ 2 - 1))
    (W : ↥(StatedSp 2 K)) (hW : W ∈ 𝔄) (c a : Fin 2 → K) (hc : c ≠ 0) (ha : a ≠ 0)
    (hWc : lv2m W *ᵥ Sum.elim c 0 = Sum.elim a 0) (n : ↥(StatedSp 2 K)) (hn : n ∈ lv2N K) :
    W * n * W⁻¹ ∈ lv2N K := by
  set Kp : Subgroup ↥(StatedSp 2 K) := lv2K (Sum.elim a 0) ⊓ 𝔄 with hKp
  have hNK : lv2N K ≤ Kp := fun m hm =>
    Subgroup.mem_inf.mpr ⟨lv2_N_le_K a ha m hm, hN hm⟩
  have hKle : Kp ≤ 𝔄 := inf_le_right
  have hexp : ∀ g ∈ Kp, g ^ 4 = 1 := fun g hg => lv2K_pow_four _ g (Subgroup.mem_inf.mp hg).1
  have hWK : W * n * W⁻¹ ∈ Kp := by
    refine Subgroup.mem_inf.mpr ⟨lv2_conj_N_mem_K W c a hc hWc n hn, ?_⟩
    exact 𝔄.mul_mem (𝔄.mul_mem hW (hN hn)) (𝔄.inv_mem hW)
  have hq2 : 2 ∣ Nat.card K := lv2_two_dvd_card
  have heq := lv2_eq_of_two_group 𝔄 Kp (lv2N K) hNK hKle hexp (Nat.card K) hq2 hK hcard
    (lv2N_card)
  rw [← heq] at hWK
  exact hWK

section Step3

variable {K : Type} [Field K]

theorem lv2Theta_injective [CharP K 2] : Function.Injective (lv2Theta (K := K)) := by
  intro h h' hhh
  have hm : lv2Blk (h : Matrix (Fin 2) (Fin 2) K) = lv2Blk (h' : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg lv2m hhh
    rw [lv2m_theta, lv2m_theta] at this
    exact this
  have e00 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inl 0)
  have e01 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inr 1)
  have e10 := congrFun (congrFun hm (Sum.inr 0)) (Sum.inl 1)
  have e11 := congrFun (congrFun hm (Sum.inr 1)) (Sum.inr 1)
  simp [lv2Blk, S0, Matrix.one_apply] at e00 e01 e10 e11
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem lv2_fromBlocks_mulVec_elim (A B C D : Matrix (Fin 2) (Fin 2) K) (x y : Fin 2 → K) :
    Matrix.fromBlocks A B C D *ᵥ Sum.elim x y = Sum.elim (A *ᵥ x + B *ᵥ y) (C *ᵥ x + D *ᵥ y) := by
  rw [Matrix.fromBlocks_mulVec]
  funext i
  rcases i with i | i <;> rfl

theorem lv2Fa_card [Finite K] [CharP K 2] :
    Nat.card (lv2Fa K) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  unfold lv2Fa
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective lv2Theta_injective,
    Subgroup.card_top]

theorem lv2_sym_of_gram (P R : Matrix (Fin 2) (Fin 2) K) (hg : Pᵀ * R = Rᵀ * P)
    (hR : R.det ≠ 0) : (P * R⁻¹)ᵀ = P * R⁻¹ := by
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
  have hR1 : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hR2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hPt : Pᵀ = Rᵀ * P * R⁻¹ := by
    calc Pᵀ = Pᵀ * (R * R⁻¹) := by rw [hR1, Matrix.mul_one]
      _ = (Pᵀ * R) * R⁻¹ := by rw [Matrix.mul_assoc]
      _ = (Rᵀ * P) * R⁻¹ := by rw [hg]
  rw [Matrix.transpose_mul, hPt]
  have hRt : (R⁻¹)ᵀ * Rᵀ = 1 := by
    rw [← Matrix.transpose_mul, hR1, Matrix.transpose_one]
  calc (R⁻¹)ᵀ * (Rᵀ * P * R⁻¹) = ((R⁻¹)ᵀ * Rᵀ) * P * R⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = P * R⁻¹ := by rw [hRt, Matrix.one_mul]

theorem lv2_uSp_inv_m (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) :
    lv2m (uSp S hS)⁻¹ = uS (-S) := rfl

theorem lv2_uSp_m (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) :
    lv2m (uSp S hS) = uS S := rfl

theorem lv2_conj_upE_comm [CharP K 2] (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) (μ : K) :
    (uSp S hS)⁻¹ * lv2upE μ * uSp S hS = lv2upE μ := by
  apply Subtype.ext
  apply Units.ext
  change lv2m ((uSp S hS)⁻¹ * lv2upE μ * uSp S hS) = lv2m (lv2upE μ)
  rw [lv2m_mul, lv2m_mul, lv2_uSp_inv_m, lv2_uSp_m, lv2m_upE]
  unfold lv2up
  rw [uS_mul, uS_mul]
  congr 1
  abel

theorem lv2_step3 [Finite K] [CharP K 2] (𝔄 : Subgroup ↥(StatedSp 2 K))
    (hN : lv2N K ≤ 𝔄) (hcard : Nat.card 𝔄 = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K))
    (W : ↥(StatedSp 2 K)) (hW : W ∈ 𝔄) (P Q R T : Matrix (Fin 2) (Fin 2) K)
    (hWm : lv2m W = Matrix.fromBlocks P Q R T) (hR : R.det ≠ 0) :
    ∃ (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S), ∀ g : ↥(StatedSp 2 K),
      g ∈ 𝔄 ↔ (uSp S hS)⁻¹ * g * uSp S hS ∈ lv2Fa K := by
  have hgram : (lv2m W)ᵀ * lv2J * lv2m W = lv2J := StatedAPI.mem_statedSp_iff.mp W.2
  rw [hWm] at hgram
  obtain ⟨g1, -, -, -⟩ := (lv2_gram_iff P Q R T).mp hgram
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
  have hR1 : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hR2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hSR : (P * R⁻¹) * R = P := by rw [Matrix.mul_assoc, hR2, Matrix.mul_one]
  have hS : (P * R⁻¹)ᵀ = P * R⁻¹ := lv2_sym_of_gram P R g1 hR
  refine ⟨P * R⁻¹, hS, ?_⟩
  set S : Matrix (Fin 2) (Fin 2) K := P * R⁻¹ with hSdef
  set u : ↥(StatedSp 2 K) := uSp S hS with hu
  set W' : ↥(StatedSp 2 K) := u⁻¹ * W with hW'def
  have hW'm : lv2m W' = Matrix.fromBlocks 0 (Q - S * T) R T := by
    rw [hW'def, lv2m_mul, hu, lv2_uSp_inv_m, hWm]
    unfold uS
    rw [Matrix.fromBlocks_multiply]
    simp [hSR, Matrix.neg_mul, sub_eq_add_neg]
  set 𝔄' : Subgroup ↥(StatedSp 2 K) := 𝔄.map (MulAut.conj u⁻¹).toMonoidHom with h𝔄'
  have hmem' : ∀ g, g ∈ 𝔄' ↔ ∃ h ∈ 𝔄, u⁻¹ * h * u = g := by
    intro g
    rw [h𝔄', Subgroup.mem_map]
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, inv_inv]
  have hcard' : Nat.card 𝔄' = Nat.card 𝔄 :=
    Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective
  have hNA : ∀ μ : K, lv2upE μ ∈ 𝔄' := fun μ => by
    rw [hmem']
    exact ⟨lv2upE μ, hN ⟨μ, rfl⟩, lv2_conj_upE_comm S hS μ⟩
  set X : Subgroup ↥(StatedSp 2 K) := (lv2N K).map (MulAut.conj W').toMonoidHom with hXdef
  have hXcard : Nat.card X = Nat.card K := by
    rw [hXdef, Subgroup.card_map_of_injective (MulAut.conj W').injective, lv2N_card]
  have hXle : X ≤ lv2Nm K := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨μ, hμ⟩ := hn
    have halt : lv2Alt n := by
      intro v
      rw [hμ]
      exact lv2up_alt μ v
    have hfix : ∀ z : Fin 2 → K, lv2m (W' * n * W'⁻¹) *ᵥ Sum.elim (0 : Fin 2 → K) z =
        Sum.elim (0 : Fin 2 → K) z := by
      intro z
      have hWa : lv2m W' *ᵥ Sum.elim (R⁻¹ *ᵥ z) (0 : Fin 2 → K) = Sum.elim (0 : Fin 2 → K) z := by
        rw [hW'm, lv2_fromBlocks_mulVec_elim]
        simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, zero_add, Matrix.mulVec_mulVec,
          hR1, Matrix.one_mulVec, Matrix.zero_mul]
      have hinv : lv2m W'⁻¹ *ᵥ Sum.elim (0 : Fin 2 → K) z = Sum.elim (R⁻¹ *ᵥ z) 0 := by
        rw [← hWa, Matrix.mulVec_mulVec, lv2m_inv_mul, Matrix.one_mulVec]
      have hnfix : lv2m n *ᵥ Sum.elim (R⁻¹ *ᵥ z) 0 = Sum.elim (R⁻¹ *ᵥ z) 0 := by
        rw [hμ, lv2up_fix]
      simp only [lv2m_mul, ← Matrix.mulVec_mulVec]
      rw [hinv, hnfix, hWa]
    obtain ⟨μ', hμ'⟩ := lv2_block_lower (W' * n * W'⁻¹) hfix (lv2Alt_conj W' n halt)
    exact ⟨μ', hμ'⟩
  have hXeq : X = lv2Nm K :=
    Subgroup.eq_of_le_of_card_ge hXle (by rw [lv2Nm_card, hXcard])
  have hNmA : ∀ μ : K, lv2lowE μ ∈ 𝔄' := fun μ => by
    have hm : lv2lowE μ ∈ X := by
      rw [hXeq]
      exact ⟨μ, rfl⟩
    obtain ⟨n, hn, hnt⟩ := Subgroup.mem_map.mp hm
    rw [hmem']
    refine ⟨W * n * W⁻¹, 𝔄.mul_mem (𝔄.mul_mem hW (hN hn)) (𝔄.inv_mem hW), ?_⟩
    rw [← hnt]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hW'def]
    group
  have hFa : lv2Fa K ≤ 𝔄' := by
    rintro _ ⟨h, rfl⟩
    exact lv2Theta_mem_of_roots 𝔄' hNA hNmA h
  have heq : lv2Fa K = 𝔄' :=
    Subgroup.eq_of_le_of_card_ge hFa (by rw [hcard', hcard, lv2Fa_card])
  intro g
  constructor
  · intro hg
    have h1 : u⁻¹ * g * u ∈ 𝔄' := (hmem' _).mpr ⟨g, hg, rfl⟩
    rw [← heq] at h1
    exact h1
  · intro hg
    rw [heq, hmem'] at hg
    obtain ⟨h, hh, hhg⟩ := hg
    have : h = g := by
      have := hhg
      exact mul_left_cancel (mul_right_cancel this)
    rw [← this]
    exact hh

@[expose] def lv2U (K : Type) [Field K] [CharP K 2] : Subgroup ↥(StatedSp 2 K) where
  carrier := {g | ∃ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S ∧ lv2m g = uS S}
  one_mem' := ⟨0, Matrix.transpose_zero, by rw [lv2m_one, uS_zero]⟩
  mul_mem' := by
    rintro g h ⟨S, hS, hg⟩ ⟨S', hS', hh⟩
    refine ⟨S + S', by rw [Matrix.transpose_add, hS, hS'], ?_⟩
    rw [lv2m_mul, hg, hh, uS_mul]
  inv_mem' := by
    rintro g ⟨S, hS, hg⟩
    refine ⟨-S, by rw [Matrix.transpose_neg, hS], ?_⟩
    have h1 := lv2m_inv_mul g
    have h2 : uS S * uS (-S) = 1 := by
      rw [uS_mul, add_neg_cancel, uS_zero]
    calc lv2m g⁻¹ = lv2m g⁻¹ * (uS S * uS (-S)) := by rw [h2, mul_one]
      _ = lv2m g⁻¹ * lv2m g * uS (-S) := by rw [hg, mul_assoc]
      _ = uS (-S) := by rw [h1, one_mul]

theorem lv2U_eq_siegel [CharP K 2] : KFacts.siegelRadical K = lv2U K := by
  apply le_antisymm
  · unfold KFacts.siegelRadical
    rw [Subgroup.closure_le]
    rintro g ⟨S, hS, hg⟩
    exact ⟨S, hS, hg⟩
  · rintro g ⟨S, hS, hg⟩
    exact Subgroup.subset_closure ⟨S, hS, hg⟩

theorem lv2_levi_conj_uS (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1)
    (S : Matrix (Fin 2) (Fin 2) K) :
    Matrix.fromBlocks A⁻¹ 0 0 Aᵀ * uS S * Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ =
      uS (A⁻¹ * S * (A⁻¹)ᵀ) := by
  have hAu : IsUnit A.det := by rw [hA]; exact isUnit_one
  have hA' : (A⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv, hA, Ring.inverse_one]
  have key := levGL_conj_uS hA' S
  rw [Matrix.nonsing_inv_nonsing_inv A hAu] at key
  exact key

theorem lv2_conj_levi_U [CharP K 2] (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1)
    (s : ↥(StatedSp 2 K)) (hs : s ∈ lv2U K) :
    (levSp A hA)⁻¹ * s * levSp A hA ∈ lv2U K := by
  obtain ⟨S, hS, hsS⟩ := hs
  refine ⟨A⁻¹ * S * (A⁻¹)ᵀ, ?_, ?_⟩
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hS, Matrix.mul_assoc]
  · rw [lv2m_mul, lv2m_mul, hsS]
    rw [show lv2m (levSp A hA)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 Aᵀ from levSp_inv_val hA,
      lv2m_levSp]
    exact lv2_levi_conj_uS A hA S

theorem lv2_decomp [Finite K] [CharP K 2] (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) :
    ∃ v : Fin 2 → K, ∃ κ : K, S = Matrix.vecMulVec v v + κ • (S0 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨r0, hr0⟩ := KFacts.Sp4TwistedLevi.exists_sq_eq (K := K) 1 (S 0 0) one_ne_zero
  obtain ⟨r1, hr1⟩ := KFacts.Sp4TwistedLevi.exists_sq_eq (K := K) 1 (S 1 1) one_ne_zero
  have h01 : S 1 0 = S 0 1 := by
    have := congrFun (congrFun hS 0) 1
    simpa using this
  refine ⟨![r0, r1], S 0 1 - r0 * r1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S0, Matrix.vecMulVec_apply, h01] <;>
    first
    | ring1
    | linear_combination (-1 : K) * hr0
    | linear_combination (-1 : K) * hr1

theorem lv2_SL_with_col [CharP K 2] (v : Fin 2 → K) (hv : v ≠ 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 ∧ A 0 0 = v 0 ∧ A 1 0 = v 1 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨!![0, (v 1)⁻¹; v 1, 0], ?_, by simp [h0], by simp⟩
    rw [Matrix.det_fin_two]
    simp [CharTwo.neg_eq, inv_mul_cancel₀ h1]
  · refine ⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_, by simp, by simp⟩
    rw [Matrix.det_fin_two]
    simp [mul_inv_cancel₀ h0]

theorem lv2_uSp_conj_single [CharP K 2] (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1)
    (v : Fin 2 → K) (hv0 : A 0 0 = v 0) (hv1 : A 1 0 = v 1)
    (hs : (Matrix.vecMulVec v v)ᵀ = Matrix.vecMulVec v v)
    (hs0 : (Matrix.single 0 0 (1 : K) : Matrix (Fin 2) (Fin 2) K)ᵀ =
      Matrix.single 0 0 (1 : K)) :
    levSp A hA * uSp (Matrix.single 0 0 (1 : K)) hs0 * (levSp A hA)⁻¹ =
      uSp (Matrix.vecMulVec v v) hs := by
  apply Subtype.ext
  apply Units.ext
  change lv2m (levSp A hA * uSp _ hs0 * (levSp A hA)⁻¹) = lv2m (uSp _ hs)
  rw [lv2m_mul, lv2m_mul, lv2m_levSp, show lv2m (levSp A hA)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 Aᵀ
    from levSp_inv_val hA]
  show Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * uS (Matrix.single 0 0 (1 : K)) *
      Matrix.fromBlocks A⁻¹ 0 0 Aᵀ = uS (Matrix.vecMulVec v v)
  have key : Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * uS (Matrix.single 0 0 (1 : K)) *
      Matrix.fromBlocks A⁻¹ 0 0 Aᵀ = uS (A * Matrix.single 0 0 (1 : K) * Aᵀ) :=
    levGL_conj_uS hA _
  rw [key]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply, hv0, hv1,
      Matrix.single_apply]

theorem lv2_step4 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (𝔄 : Subgroup ↥(StatedSp 2 K))
    (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S)
    (hiff : ∀ g : ↥(StatedSp 2 K), g ∈ 𝔄 ↔ (uSp S hS)⁻¹ * g * uSp S hS ∈ lv2Fa K) :
    𝔄 ≤ Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)) ∨
      KFacts.siegelRadical K ≤ leviSL2 K ⊔ 𝔄 := by
  obtain ⟨v, κ, hdec⟩ := lv2_decomp S hS
  have hvs : (Matrix.vecMulVec v v)ᵀ = Matrix.vecMulVec v v := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_comm]
  have hκs : (κ • (S0 : Matrix (Fin 2) (Fin 2) K))ᵀ = κ • S0 := by
    rw [Matrix.transpose_smul, lv2_S0_transpose]
  set x : ↥(StatedSp 2 K) := uSp (Matrix.vecMulVec v v) hvs with hxdef
  set n : ↥(StatedSp 2 K) := uSp (κ • (S0 : Matrix (Fin 2) (Fin 2) K)) hκs with hndef
  have hun : uSp S hS = x * n := by
    apply Subtype.ext
    apply Units.ext
    change uS S = uS (Matrix.vecMulVec v v) * uS (κ • S0)
    rw [uS_mul, hdec]
  have hnFa : n ∈ lv2Fa K := by
    refine MonoidHom.mem_range.mpr ⟨unipSL κ, ?_⟩
    rw [lv2Theta_unipSL]
    apply Subtype.ext
    apply Units.ext
    rfl
  have hconj : ∀ y : ↥(StatedSp 2 K), n⁻¹ * y * n ∈ lv2Fa K ↔ y ∈ lv2Fa K := by
    intro y
    constructor
    · intro h
      have := (lv2Fa K).mul_mem ((lv2Fa K).mul_mem hnFa h) ((lv2Fa K).inv_mem hnFa)
      simpa [mul_assoc] using this
    · intro h
      exact (lv2Fa K).mul_mem ((lv2Fa K).mul_mem ((lv2Fa K).inv_mem hnFa) h) hnFa
  have hiff' : ∀ g : ↥(StatedSp 2 K), g ∈ 𝔄 ↔ x⁻¹ * g * x ∈ lv2Fa K := by
    intro g
    rw [hiff g, hun]
    have e : (x * n)⁻¹ * g * (x * n) = n⁻¹ * (x⁻¹ * g * x) * n := by group
    rw [e, hconj]
  by_cases hv : v = 0
  · left
    have hvv : Matrix.vecMulVec v v = 0 := by
      ext i j
      simp [hv, Matrix.vecMulVec_apply]
    have hx1 : x = 1 := by
      apply Subtype.ext
      apply Units.ext
      change uS (Matrix.vecMulVec v v) = 1
      rw [hvv, uS_zero]
    intro g hg
    rw [← lv2Fa_eq_centralizer]
    have h1 := (hiff' g).mp hg
    rwa [hx1, inv_one, one_mul, mul_one] at h1
  · right
    obtain ⟨A, hA, hA0, hA1⟩ := lv2_SL_with_col v hv
    have hs0 : (Matrix.single 0 0 (1 : K) : Matrix (Fin 2) (Fin 2) K)ᵀ =
        Matrix.single 0 0 (1 : K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]
    set f : ↥(StatedSp 2 K) := levSp A hA with hfdef
    set x0 : ↥(StatedSp 2 K) := uSp (Matrix.single 0 0 (1 : K)) hs0 with hx0def
    have hxf : x = f * x0 * f⁻¹ := (lv2_uSp_conj_single A hA v hA0 hA1 hvs hs0).symm
    have hfF : f ∈ leviSL2 K := levSp_mem_levi hA
    have hC1 := KFacts.sp4TwistedLevi_holds K hK 1 x0 one_ne_zero rfl
    set 𝔅 : Subgroup ↥(StatedSp 2 K) := 𝔄.map (MulAut.conj f⁻¹).toMonoidHom with h𝔅
    have hmem𝔅 : ∀ g, g ∈ 𝔅 ↔ ∃ h ∈ 𝔄, f⁻¹ * h * f = g := by
      intro g
      rw [h𝔅, Subgroup.mem_map]
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, inv_inv]
    have hmap : (Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K))).map
        (MulAut.conj x0).toMonoidHom ≤ 𝔅 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← lv2Fa_eq_centralizer] at hy
      have hyc : f⁻¹ * y * f = y := by
        have hc := Subgroup.mem_centralizer_iff.mp (lv2Fa_le_centralizer hy) f hfF
        rw [mul_assoc, ← hc, inv_mul_cancel_left]
      rw [hmem𝔅]
      refine ⟨x * y * x⁻¹, ?_, ?_⟩
      · rw [hiff']
        have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
        rw [e]
        exact hy
      · have e : f⁻¹ * (x * y * x⁻¹) * f = x0 * (f⁻¹ * y * f) * x0⁻¹ := by
          rw [hxf]
          group
        rw [e, hyc]
        rfl
    have hsub : KFacts.siegelRadical K ≤ leviSL2 K ⊔ 𝔅 :=
      hC1.trans (sup_le_sup_left hmap _)
    have hΨ : leviSL2 K ⊔ 𝔅 ≤ (leviSL2 K ⊔ 𝔄).comap (MulAut.conj f).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro b hb
        rw [Subgroup.mem_comap]
        show f * b * f⁻¹ ∈ leviSL2 K ⊔ 𝔄
        exact Subgroup.mem_sup_left
          ((leviSL2 K).mul_mem ((leviSL2 K).mul_mem hfF hb) ((leviSL2 K).inv_mem hfF))
      · intro g hg
        obtain ⟨h, hh, hfg⟩ := (hmem𝔅 g).mp hg
        rw [Subgroup.mem_comap]
        show f * g * f⁻¹ ∈ leviSL2 K ⊔ 𝔄
        rw [← hfg]
        have e : f * (f⁻¹ * h * f) * f⁻¹ = h := by group
        rw [e]
        exact Subgroup.mem_sup_right hh
    rw [lv2U_eq_siegel]
    rintro s hs
    have hs' : f⁻¹ * s * f ∈ KFacts.siegelRadical K := by
      rw [lv2U_eq_siegel]
      exact lv2_conj_levi_U A hA s hs
    have hm := hΨ (hsub hs')
    rw [Subgroup.mem_comap] at hm
    have e : f * (f⁻¹ * s * f) * f⁻¹ = s := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hm
    rw [e] at hm
    exact hm

theorem lv2_core [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (𝔄 : Subgroup ↥(StatedSp 2 K))
    (hN : lv2N K ≤ 𝔄) (hcard : Nat.card 𝔄 = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K))
    (hnn : ∃ w ∈ 𝔄, ∃ k ∈ lv2N K, w * k * w⁻¹ ∉ lv2N K) :
    𝔄 ≤ Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)) ∨
      KFacts.siegelRadical K ≤ leviSL2 K ⊔ 𝔄 := by
  obtain ⟨w, hw, k, hk, hwk⟩ := hnn
  obtain ⟨P, Q, R, T, hWm⟩ : ∃ P Q R T : Matrix (Fin 2) (Fin 2) K,
      lv2m w = Matrix.fromBlocks P Q R T :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks (lv2m w)).symm⟩
  by_cases hdet : R.det = 0
  · exfalso
    obtain ⟨c, hc, hRc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hWc : lv2m w *ᵥ Sum.elim c (0 : Fin 2 → K) = Sum.elim (P *ᵥ c) (0 : Fin 2 → K) := by
      rw [hWm, lv2_fromBlocks_mulVec_elim, hRc]
      simp
    have ha : P *ᵥ c ≠ 0 := by
      intro h
      apply hc
      have h0 : lv2m w *ᵥ Sum.elim c (0 : Fin 2 → K) = 0 := by
        rw [hWc, h]
        simp
      have h1 : Sum.elim c (0 : Fin 2 → K) = 0 := by
        have := congrArg (fun x => lv2m w⁻¹ *ᵥ x) h0
        simpa [Matrix.mulVec_mulVec, lv2m_inv_mul] using this
      funext i
      have := congrFun h1 (Sum.inl i)
      simpa using this
    exact hwk (lv2_step2 hK 𝔄 hN (hcard.trans (card_SL2_eq K)) w hw c (P *ᵥ c) hc ha hWc k hk)
  · have hW' := lv2_step3 𝔄 hN hcard w hw P Q R T hWm hdet
    obtain ⟨S, hS, hiff⟩ := hW'
    exact lv2_step4 hK 𝔄 S hS hiff

theorem lv2U_comm [CharP K 2] (s t : ↥(StatedSp 2 K)) (hs : s ∈ lv2U K) (ht : t ∈ lv2U K) :
    s * t = t * s := by
  obtain ⟨S, hS, hsS⟩ := hs
  obtain ⟨T, hT, htT⟩ := ht
  apply Subtype.ext
  apply Units.ext
  change lv2m (s * t) = lv2m (t * s)
  rw [lv2m_mul, lv2m_mul, hsS, htT, uS_mul, uS_mul, add_comm]

theorem lv2U_sq [CharP K 2] (s : ↥(StatedSp 2 K)) (hs : s ∈ lv2U K) : s * s = 1 := by
  obtain ⟨S, hS, hsS⟩ := hs
  apply Subtype.ext
  apply Units.ext
  change lv2m (s * s) = lv2m 1
  rw [lv2m_mul, hsS, uS_mul, CharTwo.add_self_eq_zero, uS_zero, lv2m_one]

theorem lv2N_le_lv2U [CharP K 2] : lv2N K ≤ lv2U K := by
  rintro g ⟨μ, hμ⟩
  refine ⟨μ • (S0 : Matrix (Fin 2) (Fin 2) K), ?_, hμ⟩
  rw [Matrix.transpose_smul, lv2_S0_transpose]

theorem lv2_psi_line [CharP K 2] (c : K) (h : (act0E (unipSL c) : T3E K) ∈ CC) :
    psi (⟨act0E (unipSL c), h⟩ : ↥CC) = lv2upE c := by
  apply Subtype.ext
  apply Units.ext
  change lv2m (psi (⟨act0E (unipSL c), h⟩ : ↥CC)) = lv2m (lv2upE c)
  rw [lv2m_upE]
  change psiMat (⟨act0E (unipSL c), h⟩ : ↥CC) = lv2up c
  rw [psiMat_of_line rfl]
  rfl

theorem lv2_psi_rowCC [CharP K 2] (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    psi (rowCC A : ↥CC) = levSp (A : Matrix (Fin 2) (Fin 2) K) A.2 := by
  apply Subtype.ext
  apply Units.ext
  change lv2m (psi (rowCC A : ↥CC)) = lv2m (levSp (A : Matrix (Fin 2) (Fin 2) K) A.2)
  rw [lv2m_levSp]
  change psiMat (rowCC A : ↥CC) = _
  exact psiMat_rowCC A

theorem lv2U_card_ge [Finite K] [CharP K 2] : Nat.card K ^ 3 ≤ Nat.card (lv2U K) := by
  have hsym : ∀ t : K × K × K,
      (!![t.1, t.2.1; t.2.1, t.2.2] : Matrix (Fin 2) (Fin 2) K)ᵀ =
        !![t.1, t.2.1; t.2.1, t.2.2] := by
    intro t
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  let f : K × K × K → lv2U K := fun t =>
    ⟨uSp !![t.1, t.2.1; t.2.1, t.2.2] (hsym t), ⟨_, hsym t, rfl⟩⟩
  have hf : Function.Injective f := by
    intro t t' h
    have h1 : uS (!![t.1, t.2.1; t.2.1, t.2.2] : Matrix (Fin 2) (Fin 2) K) =
        uS (!![t'.1, t'.2.1; t'.2.1, t'.2.2] : Matrix (Fin 2) (Fin 2) K) :=
      congrArg (fun x : lv2U K => lv2m (x : ↥(StatedSp 2 K))) h
    have h2 := uS_injective h1
    have e0 := congrFun (congrFun h2 0) 0
    have e1 := congrFun (congrFun h2 0) 1
    have e2 := congrFun (congrFun h2 1) 1
    simp at e0 e1 e2
    exact Prod.ext e0 (Prod.ext e1 e2)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod] at this
  calc Nat.card K ^ 3 = Nat.card K * (Nat.card K * Nat.card K) := by ring
    _ ≤ Nat.card (lv2U K) := this

theorem lv2_rowG_le_CC [CharP K 2] : (rowG (K := K) : Subgroup (T3E K)) ≤ CC := by
  rintro _ ⟨A, rfl⟩
  exact (rowCC A).2

end Step3

theorem ct2_free {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (𝒜 : Subgroup (T3E K)) (h𝒜O : 𝒜 ≤ Ok 0) (h𝒜c : ∀ a ∈ 𝒜, ∀ g ∈ colG, a * g = g * a)
    (hsimp : ∀ 𝒦 : Subgroup (T3E K), 𝒦 ≤ 𝒜 → (∀ a ∈ 𝒜, ∀ k ∈ 𝒦, a * k * a⁻¹ ∈ 𝒦) →
      𝒦 = ⊥ ∨ 𝒦 = 𝒜)
    (hy : ∃ y ∈ 𝒜, NotTwoPow y) (hline : lineG ≤ 𝒜)
    (hcard : Nat.card 𝒜 = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K))
    (hbound : ∀ 𝒰 : Subgroup (T3E K), 𝒰 ≤ Ok 0 → (∀ u ∈ 𝒰, ∀ g ∈ colG, u * g = g * u) →
      (∀ u ∈ 𝒰, ∀ l ∈ lineG, u * l = l * u) →
      𝒰 ≤ Subgroup.closure ((𝒜 : Set (T3E K)) ∪
        ((rowG (K := K) : Subgroup (T3E K)) : Set (T3E K))) →
      (∀ u ∈ 𝒰, u * u = 1) → Nat.card 𝒰 ≤ 2 * Nat.card K ^ 2) :
    ∀ a ∈ 𝒜, ∀ r ∈ rowG, a * r = r * a := by
  have h𝒜 : 𝒜 ≤ CC := fun a ha => mem_CC.2 ⟨h𝒜O ha, fun g hg => (h𝒜c a ha g hg).symm⟩
  have hline' : (lineG : Subgroup (T3E K)) ≤ CC := hline.trans h𝒜
  set 𝔄 : Subgroup ↥(StatedSp 2 K) := (𝒜.comap CC.subtype).map psi with h𝔄
  have hmem𝔄 : ∀ z : ↥CC, (z : T3E K) ∈ 𝒜 → psi z ∈ 𝔄 := fun z hz =>
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hN : lv2N K ≤ 𝔄 := by
    rintro n ⟨μ, hμ⟩
    have hl : (act0E (unipSL μ) : T3E K) ∈ CC := hline' (mem_lineG_iff.mpr ⟨μ, rfl⟩)
    have hn : n = lv2upE μ := Subtype.ext (Units.ext hμ)
    rw [hn, ← lv2_psi_line μ hl]
    exact hmem𝔄 ⟨_, hl⟩ (hline (mem_lineG_iff.mpr ⟨μ, rfl⟩))
  have hcard𝔄 : Nat.card 𝔄 = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    have h1 : Nat.card 𝔄 = Nat.card (𝒜.comap CC.subtype) :=
      Subgroup.card_map_of_injective psi_injective
    have h2 : Nat.card (𝒜.comap CC.subtype) = Nat.card 𝒜 := by
      rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective CC),
        Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.mpr h𝒜]
    rw [h1, h2, hcard]
  have hT : ∃ w ∈ 𝒜, ∃ k ∈ (lineG : Subgroup (T3E K)), w * k * w⁻¹ ∉ lineG := by
    by_contra hcon
    push Not at hcon
    rcases hsimp lineG hline (fun a ha k hk => hcon a ha k hk) with h | h
    · exact lineG_ne_bot h
    · obtain ⟨y, hy𝒜, hy2⟩ := hy
      have hyl : y ∈ (lineG : Subgroup (T3E K)) := by
        rw [h]
        exact hy𝒜
      exact hy2 1 (by rw [pow_one, pow_two]; exact unip_sq y hyl)
  have hnn : ∃ w ∈ 𝔄, ∃ k ∈ lv2N K, w * k * w⁻¹ ∉ lv2N K := by
    obtain ⟨w, hw, k, hk, hwk⟩ := hT
    have hwC : w ∈ CC := h𝒜 hw
    have hkC : k ∈ CC := hline' hk
    refine ⟨psi ⟨w, hwC⟩, hmem𝔄 ⟨w, hwC⟩ hw, psi ⟨k, hkC⟩, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := mem_lineG_iff.mp hk
      have h' : (⟨k, hkC⟩ : ↥CC) = ⟨act0E (unipSL c), hline' (mem_lineG_iff.mpr ⟨c, rfl⟩)⟩ :=
        Subtype.ext hc
      rw [h', lv2_psi_line]
      exact ⟨c, rfl⟩
    · intro hmem
      apply hwk
      obtain ⟨μ, hμ⟩ := hmem
      have hz : psi (⟨w, hwC⟩ * ⟨k, hkC⟩ * ⟨w, hwC⟩⁻¹) = lv2upE μ := by
        rw [map_mul, map_mul, map_inv]
        exact Subtype.ext (Units.ext hμ)
      have hl : (act0E (unipSL μ) : T3E K) ∈ CC := hline' (mem_lineG_iff.mpr ⟨μ, rfl⟩)
      have hzl : (⟨w, hwC⟩ * ⟨k, hkC⟩ * ⟨w, hwC⟩⁻¹ : ↥CC) = ⟨act0E (unipSL μ), hl⟩ :=
        psi_injective (hz.trans (lv2_psi_line μ hl).symm)
      have h5 := congrArg Subtype.val hzl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
      rw [h5]
      exact mem_lineG_iff.mpr ⟨μ, rfl⟩
  rcases lv2_core hK 𝔄 hN hcard𝔄 hnn with hC | hSR
  · rintro a ha _ ⟨A, rfl⟩
    have haC : a ∈ CC := h𝒜 ha
    have hψa := hmem𝔄 ⟨a, haC⟩ ha
    have hψr : psi (rowCC A) ∈ leviSL2 K := by
      rw [lv2_psi_rowCC]
      exact levSp_mem_levi _
    have hcomm := Subgroup.mem_centralizer_iff.mp (hC hψa) _ hψr
    have h2 : psi ((rowCC A : ↥CC) * ⟨a, haC⟩) = psi (⟨a, haC⟩ * (rowCC A : ↥CC)) := by
      rw [map_mul, map_mul, hcomm]
    exact (congrArg Subtype.val (psi_injective h2)).symm
  exfalso
  set 𝔊 : Subgroup (T3E K) := Subgroup.closure ((𝒜 : Set (T3E K)) ∪
    ((rowG (K := K) : Subgroup (T3E K)) : Set (T3E K))) with h𝔊
  have h𝔊CC : 𝔊 ≤ CC := (Subgroup.closure_le _).mpr (Set.union_subset h𝒜 lv2_rowG_le_CC)
  have h𝒜𝔊 : 𝒜 ≤ 𝔊 := fun a ha => Subgroup.subset_closure (Or.inl ha)
  set 𝒢C : Subgroup ↥CC := 𝔊.comap CC.subtype with h𝒢C
  have hFb𝒢 : leviSL2 K ≤ 𝒢C.map psi := by
    rw [leviSL2, Subgroup.closure_le]
    rintro g ⟨A, hA, hg⟩
    have hgl : g = levSp A hA := Subtype.ext (Units.ext hg)
    rw [hgl, ← lv2_psi_rowCC ⟨A, hA⟩]
    refine Subgroup.mem_map_of_mem psi ?_
    exact Subgroup.mem_comap.mpr (Subgroup.subset_closure (Or.inr ⟨⟨A, hA⟩, rfl⟩))
  have hA𝒢 : 𝔄 ≤ 𝒢C.map psi := Subgroup.map_mono (Subgroup.comap_mono h𝒜𝔊)
  have hsup : leviSL2 K ⊔ 𝔄 ≤ 𝒢C.map psi := sup_le hFb𝒢 hA𝒢
  set 𝒰C : Subgroup ↥CC := 𝒢C ⊓ (lv2U K).comap psi with h𝒰C
  set 𝒰 : Subgroup (T3E K) := 𝒰C.map CC.subtype with h𝒰
  have h𝒰𝔊 : 𝒰 ≤ 𝔊 := by
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hz).1
  have hb := hbound 𝒰 (fun u hu => (mem_CC.mp (h𝔊CC (h𝒰𝔊 hu))).1)
    (by
      rintro u hu g hg
      obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hu
      exact ((mem_CC.mp z.2).2 g hg).symm)
    (by
      rintro u hu l hl
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu
      have hz' : psi z ∈ lv2U K := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hz).2
      have hlC : l ∈ CC := hline' hl
      obtain ⟨c, hc⟩ := mem_lineG_iff.mp hl
      have hl' : psi ⟨l, hlC⟩ ∈ lv2U K := by
        have h' : (⟨l, hlC⟩ : ↥CC) = ⟨act0E (unipSL c), hline' (mem_lineG_iff.mpr ⟨c, rfl⟩)⟩ :=
          Subtype.ext hc
        rw [h', lv2_psi_line]
        exact lv2N_le_lv2U ⟨c, rfl⟩
      have hcom := lv2U_comm _ _ hz' hl'
      have h2 : psi (z * ⟨l, hlC⟩) = psi (⟨l, hlC⟩ * z) := by
        rw [map_mul, map_mul, hcom]
      exact congrArg Subtype.val (psi_injective h2))
    h𝒰𝔊
    (by
      rintro u hu
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu
      have hz' : psi z ∈ lv2U K := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hz).2
      have h2 := lv2U_sq _ hz'
      have h3 : z * z = 1 := psi_injective (by rw [map_mul, h2, map_one])
      exact congrArg Subtype.val h3)
  have hcardU : Nat.card 𝒰 = Nat.card 𝒰C :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective CC)
  have hsurj : Nat.card (lv2U K) ≤ Nat.card 𝒰C := by
    let f : ↥𝒰C → ↥(lv2U K) := fun z =>
      ⟨psi z.1, Subgroup.mem_comap.mp (Subgroup.mem_inf.mp z.2).2⟩
    refine Nat.card_le_card_of_surjective f ?_
    rintro ⟨s, hs⟩
    have hs' : s ∈ leviSL2 K ⊔ 𝔄 := hSR (by rw [lv2U_eq_siegel]; exact hs)
    obtain ⟨z, hz, hzs⟩ := Subgroup.mem_map.mp (hsup hs')
    refine ⟨⟨z, Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_comap.mpr (by rw [hzs]; exact hs)⟩⟩, ?_⟩
    exact Subtype.ext hzs
  have hbig := lv2U_card_ge (K := K)
  rw [hcardU] at hb
  nlinarith [hbig, hsurj, hb, hK]

end Vectors

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
