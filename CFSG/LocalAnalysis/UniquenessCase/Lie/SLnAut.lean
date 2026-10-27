module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SLnTorus
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {m : ℕ} {K : Type} [Field K]

theorem uc22pwSLn_mem_unitriangular {N : ℕ} {A B D D' : Matrix (Fin N) (Fin N) K}
    {g : SpecialLinearGroup (Fin N) K} (hA : A.IsUpperTriangular) (hD : D.IsUpperTriangular)
    (hD' : D'.IsUpperTriangular) (hAB : A * B = 1) (hDD' : ∀ i, D i i * D' i i = 1)
    (hg : (g : Matrix (Fin N) (Fin N) K) = A * D * B * D') : g ∈ unitriangular N K := by
  have hB := uc22pwI3_inv_upper hA hAB
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hg]
    exact (((hA.mul hD).mul hB).mul hD') hij
  · rw [hg, mul_apply_self_of_isUpperTriangular ((hA.mul hD).mul hB) hD',
      mul_apply_self_of_isUpperTriangular (hA.mul hD) hB, mul_apply_self_of_isUpperTriangular hA hD]
    have h1 : A i i * B i i = 1 := by
      have := congrFun (congrFun hAB i) i
      rwa [mul_apply_self_of_isUpperTriangular hA hB, Matrix.one_apply_eq] at this
    calc A i i * D i i * B i i * D' i i = (A i i * B i i) * (D i i * D' i i) := by ring
      _ = 1 := by rw [h1, hDD' i, one_mul]

theorem uc22pwSLn_key_of_form (ν : MulAut (SpecialLinearGroup (Fin (m + 2)) K))
    {A B : Matrix (Fin (m + 2)) (Fin (m + 2)) K} {i : ℕ} (hA : A.IsUpperTriangular)
    (hAB : A * B = 1)
    (hform : ∀ b : Kˣ, (ν (uc22pwSLnD m K b) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
      A * diagonal (uc22pwSLnDv (b ^ 2 ^ i)) * B) (a : Kˣ) :
    ν (uc22pwSLnD m K a) * (uc22pwSLnD m K (a ^ 2 ^ i))⁻¹ ∈ unitriangular (m + 2) K := by
  rw [← map_inv]
  refine uc22pwSLn_mem_unitriangular (A := A) (B := B)
    (D := diagonal (uc22pwSLnDv (a ^ 2 ^ i)))
    (D' := diagonal (uc22pwSLnDv (a ^ 2 ^ i)⁻¹)) hA
    (Matrix.blockTriangular_diagonal _) (Matrix.blockTriangular_diagonal _) hAB ?_ ?_
  · intro r
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    have h := uc22pwSLnDv_mul (a ^ 2 ^ i) ((a ^ 2 ^ i)⁻¹) r
    rw [mul_inv_cancel] at h
    rw [← h]
    unfold uc22pwSLnDv
    split_ifs <;> simp
  · refine (Matrix.SpecialLinearGroup.coe_mul _ _).trans ?_
    rw [hform a]
    rfl

theorem uc22pwSLn_symm_mem {N : ℕ} (ν : MulAut (SpecialLinearGroup (Fin N) K))
    (hν : ∀ s, s ∈ unitriangular N K ↔ ν s ∈ unitriangular N K) :
    ∀ u ∈ unitriangular N K, ν.symm u ∈ unitriangular N K := by
  intro u hu
  exact (hν (ν.symm u)).2 (by rw [ν.apply_symm_apply u]; exact hu)

theorem uc22pwSLn_upper_of_form {N : ℕ} (ν : MulAut (SpecialLinearGroup (Fin N) K))
    (hν : ∀ s, s ∈ unitriangular N K ↔ ν s ∈ unitriangular N K) (A : GL (Fin N) K)
    (φ : K ≃+* K)
    (hmat : ∀ s : SpecialLinearGroup (Fin N) K, (ν s : Matrix (Fin N) (Fin N) K) =
      (A : Matrix (Fin N) (Fin N) K) * (s : Matrix (Fin N) (Fin N) K).map φ *
        ((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) :
    (A : Matrix (Fin N) (Fin N) K).IsUpperTriangular := by
  refine uc22pwI3_upper_of_invariant _ _ (Units.mul_inv A) (Units.inv_mul A)
    (fun u₁ hu₁ => ?_)
  have hs : ν.symm u₁ ∈ unitriangular N K := uc22pwSLn_symm_mem ν hν u₁ hu₁
  refine ⟨((ν.symm u₁ : SpecialLinearGroup (Fin N) K) :
    Matrix (Fin N) (Fin N) K).map φ, ?_, ?_⟩
  · intro k l hkl
    simp [Matrix.map_apply, hs.1 k l hkl]
  · have h1 := hmat (ν.symm u₁)
    rw [ν.apply_symm_apply u₁] at h1
    calc (u₁ : Matrix (Fin N) (Fin N) K) * (A : Matrix (Fin N) (Fin N) K)
        = ((A : Matrix (Fin N) (Fin N) K) *
          ((ν.symm u₁ : SpecialLinearGroup (Fin N) K) : Matrix (Fin N) (Fin N) K).map φ *
            ((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *
              (A : Matrix (Fin N) (Fin N) K) := by
          rw [← h1]
      _ = (A : Matrix (Fin N) (Fin N) K) *
          ((ν.symm u₁ : SpecialLinearGroup (Fin N) K) : Matrix (Fin N) (Fin N) K).map φ := by
          rw [Matrix.mul_assoc, Units.inv_mul A, Matrix.mul_one]

theorem uc22pwSLn_upper_mul_rev_of_form {N : ℕ} (ν : MulAut (SpecialLinearGroup (Fin N) K))
    (hν : ∀ s, s ∈ unitriangular N K ↔ ν s ∈ unitriangular N K) (A : GL (Fin N) K)
    (φ : K ≃+* K)
    (hmat : ∀ s : SpecialLinearGroup (Fin N) K, (ν s : Matrix (Fin N) (Fin N) K) =
      (A : Matrix (Fin N) (Fin N) K) *
        ((s⁻¹ : SpecialLinearGroup (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ.map φ *
          ((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) :
    ((A : Matrix (Fin N) (Fin N) K) * permMatrix N K Fin.revPerm).IsUpperTriangular := by
  have hJJ : permMatrix N K Fin.revPerm * permMatrix N K Fin.revPerm = 1 :=
    CFSG.LieType.SpecialLinear.permMatrix_rev_mul_self K N
  have hAB' : ((A : Matrix (Fin N) (Fin N) K) * permMatrix N K Fin.revPerm) *
      (permMatrix N K Fin.revPerm * ((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permMatrix N K Fin.revPerm), hJJ,
      Matrix.one_mul, Units.mul_inv A]
  have hBA' : (permMatrix N K Fin.revPerm *
      ((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *
        ((A : Matrix (Fin N) (Fin N) K) * permMatrix N K Fin.revPerm) = 1 := by
    rw [Matrix.mul_assoc,
      ← Matrix.mul_assoc ((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K), Units.inv_mul A,
      Matrix.one_mul, hJJ]
  refine uc22pwI3_upper_of_invariant _ _ hAB' hBA' (fun u₁ hu₁ => ?_)
  have hs : ν.symm u₁ ∈ unitriangular N K := uc22pwSLn_symm_mem ν hν u₁ hu₁
  refine ⟨permMatrix N K Fin.revPerm *
    ((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin N) K) :
      Matrix (Fin N) (Fin N) K)ᵀ).map φ * permMatrix N K Fin.revPerm, ?_, ?_⟩
  · intro k l hkl
    rw [CFSG.LieType.SpecialLinear.revGL_mul_mul, Matrix.submatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply]
    have hrev : Fin.rev k < Fin.rev l := Fin.rev_lt_rev.2 hkl
    rw [(inv_mem hs).1 (Fin.rev l) (Fin.rev k) hrev, map_zero]
  · have h1 := hmat (ν.symm u₁)
    rw [ν.apply_symm_apply u₁] at h1
    calc (u₁ : Matrix (Fin N) (Fin N) K) *
          ((A : Matrix (Fin N) (Fin N) K) * permMatrix N K Fin.revPerm)
        = ((A : Matrix (Fin N) (Fin N) K) *
          (((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin N) K) :
            Matrix (Fin N) (Fin N) K)ᵀ).map φ) *
              ((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *
            ((A : Matrix (Fin N) (Fin N) K) * permMatrix N K Fin.revPerm) := by rw [← h1]
      _ = ((A : Matrix (Fin N) (Fin N) K) * permMatrix N K Fin.revPerm) *
            (permMatrix N K Fin.revPerm *
              (((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin N) K) :
                Matrix (Fin N) (Fin N) K)ᵀ).map φ) *
                permMatrix N K Fin.revPerm) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K),
              Units.inv_mul A, Matrix.one_mul,
              ← Matrix.mul_assoc (permMatrix N K Fin.revPerm), hJJ, Matrix.one_mul]

theorem uc22pwSLn_key [Finite K] [CharP K 2] (hm : 1 ≤ m)
    (ν : MulAut (SpecialLinearGroup (Fin (m + 2)) K))
    (hν : ∀ s, s ∈ unitriangular (m + 2) K ↔ ν s ∈ unitriangular (m + 2) K) :
    ∃ i : ℕ, ∀ a : Kˣ,
      ν (uc22pwSLnD m K a) * (uc22pwSLnD m K (a ^ 2 ^ i))⁻¹ ∈ unitriangular (m + 2) K := by
  obtain ⟨A, σ, h⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (n := m + 2) (by omega) ν
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow σ
  refine ⟨i, fun a => ?_⟩
  rcases h with h | h
  · have hAup : (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K).IsUpperTriangular :=
      uc22pwSLn_upper_of_form ν hν A σ h
    have hAB : (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
        ((A⁻¹ : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) = 1 :=
      Units.mul_inv A
    exact uc22pwSLn_key_of_form ν hAup hAB (fun b => by
      rw [h, uc22pwSLnD_map hi]) a
  · have hJJ : permMatrix (m + 2) K Fin.revPerm * permMatrix (m + 2) K Fin.revPerm = 1 :=
      CFSG.LieType.SpecialLinear.permMatrix_rev_mul_self K (m + 2)
    have hAup : ((A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
        permMatrix (m + 2) K Fin.revPerm).IsUpperTriangular :=
      uc22pwSLn_upper_mul_rev_of_form ν hν A σ h
    have hAB : (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
        ((A⁻¹ : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) = 1 :=
      Units.mul_inv A
    have hAB' : ((A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
        permMatrix (m + 2) K Fin.revPerm) *
          (permMatrix (m + 2) K Fin.revPerm *
            ((A⁻¹ : GL (Fin (m + 2)) K) :
              Matrix (Fin (m + 2)) (Fin (m + 2)) K)) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permMatrix (m + 2) K Fin.revPerm), hJJ,
        Matrix.one_mul, hAB]
    exact uc22pwSLn_key_of_form ν hAup hAB' (fun b => by
      rw [h, uc22pwSLnD_graph hi]
      simp only [Matrix.mul_assoc]) a

end CFSG.LocalAnalysis.UniquenessCase.UC22
