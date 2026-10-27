module

public import CFSG.RankThree.SteinbergR3ESymplecticFrobeniusLang
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Onto

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical CFSG.Assembly.LowTwoRank

@[expose] def f4SpIndex : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 2] ![3, 1]
  invFun := ![Sum.inl 0, Sum.inr 1, Sum.inl 1, Sum.inr 0]
  left_inv := by decide
  right_inv := by decide

variable (K : Type) [Field K]

theorem reindex_f4J0 :
    (f4J0 K).reindex f4SpIndex.symm f4SpIndex.symm = fromBlocks 0 1 (-1) 0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [f4J0, f4SpIndex]

variable {K} in
theorem reindex_transpose_mul_mul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (e : m ≃ n) (A J : Matrix m m K) :
    (Aᵀ * J * A).reindex e e = (A.reindex e e)ᵀ * J.reindex e e * A.reindex e e := by
  simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

@[expose] def f4SpReindexGL : GL (Fin 4) K ≃* GL (Fin 2 ⊕ Fin 2) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K f4SpIndex.symm).toMulEquiv

theorem coe_f4SpReindexGL (A : GL (Fin 4) K) :
    ((f4SpReindexGL K A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (A : Matrix (Fin 4) (Fin 4) K).reindex f4SpIndex.symm f4SpIndex.symm :=
  rfl

theorem mem_statedSp_iff {n : ℕ} {A : GL (Fin n ⊕ Fin n) K} :
    A ∈ StatedSp n K ↔ (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      fromBlocks 0 1 (-1) 0 * (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        fromBlocks 0 1 (-1) 0 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

theorem map_f4SpReindexGL :
    (matrixIsometryGroup (f4J0 K)).map (f4SpReindexGL K).toMonoidHom = StatedSp 2 K := by
  ext B
  rw [Subgroup.mem_map_equiv, mem_matrixIsometryGroup, mem_statedSp_iff]
  have hB : B = f4SpReindexGL K ((f4SpReindexGL K).symm B) := by simp
  rw [hB, MulEquiv.symm_apply_apply, coe_f4SpReindexGL, ← reindex_f4J0,
    ← reindex_transpose_mul_mul]
  exact (Matrix.reindex f4SpIndex.symm f4SpIndex.symm).injective.eq_iff.symm

@[expose] def f4SpEquiv : matrixIsometryGroup (f4J0 K) ≃* StatedSp 2 K :=
  ((f4SpReindexGL K).subgroupMap (matrixIsometryGroup (f4J0 K))).trans
    (MulEquiv.subgroupCongr (map_f4SpReindexGL K))

theorem f4J0_map {L : Type} [Field L] (f : K →+* L) : (f4J0 K).map f = f4J0 L := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f4J0]

theorem isQuasisimple_f4Sp [Finite K] (hK : 3 ≤ Nat.card K) :
    CFSG.IsQuasisimple (matrixIsometryGroup (f4J0 K)) := by
  have hF : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ 2) ∨
      (Nat.card K = 2 ∧ 3 ≤ 2) := by
    rcases Nat.lt_or_ge (Nat.card K) 4 with h | h
    · exact Or.inr (Or.inl ⟨by omega, le_rfl⟩)
    · exact Or.inl (Or.inr h)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (f4SpEquiv K).symm
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) hF)

theorem neg_one_mem_f4Sp : (-1 : GL (Fin 4) K) ∈ matrixIsometryGroup (f4J0 K) := by
  rw [mem_matrixIsometryGroup, Units.val_neg, Units.val_one, Matrix.transpose_neg,
    Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one,
    neg_neg]

theorem mem_center_f4Sp_iff (z : matrixIsometryGroup (f4J0 K)) :
    z ∈ Subgroup.center (matrixIsometryGroup (f4J0 K)) ↔
      ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 ∨
        ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 := by
  constructor
  · intro hz
    have hz' : f4SpEquiv K z ∈ Subgroup.center (StatedSp 2 K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨y, rfl⟩ := (f4SpEquiv K).surjective g
      rw [← map_mul, ← map_mul, hz y]
    rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at hz'
    obtain ⟨d, hd⟩ := hz'
    have hmat : ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (d : K) • 1 := by
      have h1 := congrArg (fun A : GL (Fin 2 ⊕ Fin 2) K =>
        (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hd
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at h1
      change Matrix.scalar (Fin 2 ⊕ Fin 2) (d : K) =
        ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).reindex f4SpIndex.symm
          f4SpIndex.symm at h1
      apply (Matrix.reindex f4SpIndex.symm f4SpIndex.symm).injective
      rw [← h1, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      ext i j
      simp [Matrix.reindex_apply, Matrix.diagonal_apply]
    have hsq : (d : K) * d = 1 := by
      have h2 := z.2
      rw [mem_matrixIsometryGroup, hmat, Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
      have h3 := congrFun (congrFun h2 0) 3
      simp [f4J0] at h3
      exact h3
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · left
      rw [hmat, h, one_smul]
    · right
      rw [hmat, h, neg_smul, one_smul]
  · intro hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rcases hz with h | h <;> rw [h] <;> simp

theorem natCard_center_f4Sp (hK : ringChar K ≠ 2) :
    Nat.card (Subgroup.center (matrixIsometryGroup (f4J0 K))) = 2 := by
  have hne : (-1 : K) ≠ 1 := fun h => hK (neg_one_eq_one_iff.1 h)
  set m1 : matrixIsometryGroup (f4J0 K) := ⟨-1, neg_one_mem_f4Sp K⟩ with hm1def
  have hm1 : m1 ∈ Subgroup.center (matrixIsometryGroup (f4J0 K)) :=
    (mem_center_f4Sp_iff K m1).2 (Or.inr (by simp [m1]))
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨m1, hm1⟩, fun h => ?_, ?_⟩
  · have h1 := congrArg (fun z : Subgroup.center (matrixIsometryGroup (f4J0 K)) =>
      (((z : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h
    simp [m1] at h1
    exact hne (by linear_combination -h1)
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (mem_center_f4Sp_iff K z.1).1 z.2 with h | h
    · left
      exact Subtype.ext (Subtype.ext (Units.ext h))
    · right
      exact Subtype.ext (Subtype.ext (Units.ext (by rw [h]; simp [m1])))

theorem f4Sp_frobenius_lang [Finite K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : GL (Fin 4) Ω) (hA : A ∈ matrixIsometryGroup (f4J0 Ω)) :
    ∃ P ∈ matrixIsometryGroup (f4J0 Ω),
      {X : GL (Fin 4) Ω | X ∈ matrixIsometryGroup (f4J0 Ω) ∧
          (A : Matrix (Fin 4) (Fin 4) Ω) * (X : Matrix (Fin 4) (Fin 4) Ω).map (· ^ Nat.card K) *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) Ω) = X} =
        (fun Y => P * Matrix.GeneralLinearGroup.map (algebraMap K Ω) Y * P⁻¹) ''
          (matrixIsometryGroup (f4J0 K) : Set (GL (Fin 4) K)) := by
  have hdet : (f4J0 K).det ≠ 0 := by
    rw [det_f4J0]
    exact one_ne_zero
  set J : GL (Fin (2 * 2)) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (f4J0 K) hdet with hJ
  have hJm : (J : Matrix (Fin 4) (Fin 4) K) = f4J0 K := rfl
  have hJΩ : (J : Matrix (Fin 4) (Fin 4) K).map (algebraMap K Ω) = f4J0 Ω := by
    rw [hJm, f4J0_map]
  obtain ⟨P, hP, -, hset, -⟩ :=
    CFSG.RankThree.SymplecticLang.symplectic_matrix_frobenius_lang_and_exact_fixed_group
    (n := 2) (by norm_num) J (fun j => by fin_cases j <;> simp [hJm, f4J0])
    (fun j l => by fin_cases j <;> fin_cases l <;> simp [hJm, f4J0]) A (by rw [hJΩ]; exact hA)
  rw [hJΩ] at hP hset
  exact ⟨P, hP, hset⟩

theorem eq_smul_one_of_commute_f4B2_gens {L : Type*} [Field L] {M : Matrix (Fin 4) (Fin 4) L}
    (h1 : M * (1 + single 1 2 1) = (1 + single 1 2 1) * M)
    (h2 : M * (1 + single 2 1 1) = (1 + single 2 1 1) * M)
    (h3 : M * (1 + single 0 1 1 + single 2 3 1) = (1 + single 0 1 1 + single 2 3 1) * M)
    (h4 : M * (1 + single 1 0 1 + single 3 2 1) = (1 + single 1 0 1 + single 3 2 1) * M) :
    M = M 0 0 • 1 := by
  have E : ∀ (A : Matrix (Fin 4) (Fin 4) L), M * A = A * M → ∀ i j, (M * A) i j = (A * M) i j :=
    fun A h i j => by rw [h]
  have a02 := E _ h1 0 2
  have a22 := E _ h1 2 2
  have a32 := E _ h1 3 2
  have a12 := E _ h1 1 2
  have a10 := E _ h1 1 0
  have a13 := E _ h1 1 3
  have b01 := E _ h2 0 1
  have b11 := E _ h2 1 1
  have b31 := E _ h2 3 1
  have b20 := E _ h2 2 0
  have b23 := E _ h2 2 3
  have c31 := E _ h3 3 1
  have c23 := E _ h3 2 3
  have d10 := E _ h4 1 0
  have d02 := E _ h4 0 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] at a02 a22
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] at a32 a12 a10
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] at a13 b01 b11
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] at b31 b20 b23
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] at c31 c23 d10
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] at d02
  have e11 : M 1 1 = M 0 0 := by linear_combination d10
  have e22 : M 2 2 = M 0 0 := by linear_combination -a12 + d10
  have e33 : M 3 3 = M 0 0 := by linear_combination -c23 - a12 + d10
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a02, a22, a32, a10, a13, b01, b11, b31, b20, b23, c31, d02, e11, e22, e33]

end CFSG.RankThree.Chevalley
