module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
public import CFSG.Quasithin.Vol2.KGFactSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm
open Subgroup Matrix

variable {K : Type} [Field K]

@[expose] def uc22pwI3dm (a : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![(a : K), 1, ((a⁻¹ : Kˣ) : K)]

theorem uc22pwI3dm_mul (a b : Kˣ) : uc22pwI3dm (a * b) = uc22pwI3dm a * uc22pwI3dm b := by
  unfold uc22pwI3dm
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

theorem det_uc22pwI3dm (a : Kˣ) : (uc22pwI3dm a : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  unfold uc22pwI3dm
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_three]

variable (K) in
@[expose] def uc22pwI3dSL : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun a := ⟨uc22pwI3dm a, det_uc22pwI3dm a⟩
  map_one' := by
    apply Subtype.ext
    unfold uc22pwI3dm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  map_mul' a b := Subtype.ext (uc22pwI3dm_mul a b)

theorem coe_uc22pwI3dSL (a : Kˣ) :
    ((uc22pwI3dSL K a : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = uc22pwI3dm a :=
  rfl

variable (K) in
@[expose] def uc22pwI3J : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem uc22pwI3J_mul_self : uc22pwI3J K * uc22pwI3J K = 1 := by
  unfold uc22pwI3J
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem uc22pwI3J_mul_apply (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (uc22pwI3J K * M) i j = M i.rev j := by
  unfold uc22pwI3J
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> simp

theorem uc22pwI3J_apply_mul (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (M * uc22pwI3J K) i j = M i j.rev := by
  unfold uc22pwI3J
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases j <;> simp

theorem uc22pwI3J_conj (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (uc22pwI3J K * M * uc22pwI3J K) i j = M i.rev j.rev := by
  rw [uc22pwI3J_apply_mul, uc22pwI3J_mul_apply]

theorem det_uc22pwI3J [CharP K 2] : (uc22pwI3J K).det = 1 := by
  unfold uc22pwI3J
  rw [Matrix.det_fin_three]
  simp [CharTwo.neg_eq]

variable (K) in
@[expose] def uc22pwI3Jsl [CharP K 2] : SpecialLinearGroup (Fin 3) K := ⟨uc22pwI3J K, det_uc22pwI3J⟩

open Module in
theorem uc22pwI3_upper_of_invariant {n : ℕ} (g h : Matrix (Fin n) (Fin n) K) (hgh : g * h = 1)
    (hhg : h * g = 1)
    (hN : ∀ u ∈ unitriangular n K, ∃ N : Matrix (Fin n) (Fin n) K, N.IsUpperTriangular ∧
      (u : Matrix (Fin n) (Fin n) K) * g = g * N) : g.IsUpperTriangular := by
  have hinj : Function.Injective (Matrix.mulVecLin g) := by
    intro v w hvw
    have := congrArg (fun x => h *ᵥ x) hvw
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hhg] using this
  have hW : ∀ m, m ≤ n → (flagSpace n K m).map (Matrix.mulVecLin g) = flagSpace n K m := by
    intro m hm
    have hinv : ∀ u ∈ unitriangular n K, ∀ v ∈ (flagSpace n K m).map (Matrix.mulVecLin g),
        (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ (flagSpace n K m).map (Matrix.mulVecLin g) := by
      rintro u hu _ ⟨x, hx, rfl⟩
      obtain ⟨N, hNup, hN'⟩ := hN u hu
      refine ⟨N *ᵥ x, ?_, ?_⟩
      · have hx' : x ∈ flagSpace n K m := hx
        show N *ᵥ x ∈ flagSpace n K m
        rw [mem_flagSpace] at hx' ⊢
        intro k hk
        rw [Matrix.mulVec, dotProduct]
        refine Finset.sum_eq_zero fun l _ => ?_
        rcases lt_or_ge l k with hlk | hlk
        · rw [hNup hlk, zero_mul]
        · rw [hx' l (hk.trans hlk), mul_zero]
      · rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          hN']
    obtain ⟨m', hm', hW⟩ := eq_flagSpace_of_invariant hinv
    have hfin : finrank K ((flagSpace n K m).map (Matrix.mulVecLin g)) = m := by
      rw [← (Submodule.equivMapOfInjective (Matrix.mulVecLin g) hinj (flagSpace n K m)).finrank_eq,
        finrank_flagSpace hm]
    rw [hW, finrank_flagSpace hm'] at hfin
    rw [hW, hfin]
  intro i j hij
  have hj : (Pi.single j (1 : K) : Fin n → K) ∈ flagSpace n K (j + 1) := by
    rw [mem_flagSpace]
    intro k hk
    have hkj : k ≠ j := fun h => by
      rw [h] at hk
      omega
    exact Pi.single_eq_of_ne hkj _
  have h1 : g *ᵥ (Pi.single j (1 : K) : Fin n → K) ∈ flagSpace n K (j + 1) := by
    rw [← hW (j + 1) j.2]
    exact ⟨_, hj, rfl⟩
  rw [mem_flagSpace] at h1
  have h2 := h1 i (by have : (j : ℕ) < i := hij; omega)
  simpa [Matrix.mulVec_single_one] using h2

theorem uc22pwI3_inv_upper {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : A.IsUpperTriangular)
    (hAB : A * B = 1) : B.IsUpperTriangular := by
  have : Invertible A := invertibleOfRightInverse A B hAB
  rw [← Matrix.inv_eq_right_inv hAB]
  exact Matrix.blockTriangular_inv_of_blockTriangular hA

theorem uc22pwI3_mem_unitriangular {A B D D' : Matrix (Fin 3) (Fin 3) K}
    {g : SpecialLinearGroup (Fin 3) K} (hA : A.IsUpperTriangular) (hD : D.IsUpperTriangular)
    (hD' : D'.IsUpperTriangular) (hAB : A * B = 1) (hDD' : ∀ i, D i i * D' i i = 1)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = A * D * B * D') : g ∈ unitriangular 3 K := by
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

theorem uc22pwI3_matrix_zero (A : GL (Fin 3) K) (φ : K ≃+* K) (s : SpecialLinearGroup (Fin 3) K) :
    ((slConjugation 3 K A * slFieldAut (Fin 3) K φ * slGraphAut 3 K ^ 0 :
      MulAut (SpecialLinearGroup (Fin 3) K)) s : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * (s : Matrix (Fin 3) (Fin 3) K).map φ *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [pow_zero, mul_one, MulAut.mul_apply, coe_slConjugation]
  rfl

theorem uc22pwI3_matrix_one (A : GL (Fin 3) K) (φ : K ≃+* K) (s : SpecialLinearGroup (Fin 3) K) :
    ((slConjugation 3 K A * slFieldAut (Fin 3) K φ * slGraphAut 3 K ^ 1 :
      MulAut (SpecialLinearGroup (Fin 3) K)) s : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) *
        (((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ).map φ *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [pow_one, MulAut.mul_apply, MulAut.mul_apply, coe_slConjugation]
  rfl

theorem uc22pwI3_dm_map {φ : K ≃+* K} {i : ℕ} (hi : ∀ x : K, φ x = x ^ 2 ^ i) (a : Kˣ) :
    (uc22pwI3dm a : Matrix (Fin 3) (Fin 3) K).map φ = uc22pwI3dm (a ^ 2 ^ i) := by
  unfold uc22pwI3dm
  rw [Matrix.diagonal_map (by simp)]
  congr 1
  funext j
  fin_cases j <;> simp [hi]

theorem uc22pwI3_graph_dm {φ : K ≃+* K} {i : ℕ} (hi : ∀ x : K, φ x = x ^ 2 ^ i) (a : Kˣ) :
    ((((uc22pwI3dSL K a)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ).map φ =
      uc22pwI3J K * uc22pwI3dm (a ^ 2 ^ i) * uc22pwI3J K := by
  rw [← map_inv]
  have h1 : (((uc22pwI3dSL K a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      uc22pwI3dm a⁻¹ := rfl
  rw [h1]
  ext r c
  rw [uc22pwI3J_conj]
  unfold uc22pwI3dm
  rw [Matrix.diagonal_transpose]
  fin_cases r <;> fin_cases c <;> simp [Matrix.diagonal_apply, hi, Fin.rev]

theorem uc22pwI3dm_upper (c : Kˣ) : (uc22pwI3dm c : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
  intro i j hij
  unfold uc22pwI3dm
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

theorem uc22pwI3dm_diag (c : Kˣ) (r : Fin 3) :
    (uc22pwI3dm c : Matrix (Fin 3) (Fin 3) K) r r * (uc22pwI3dm c⁻¹ : Matrix (Fin 3) (Fin 3) K) r r = 1 := by
  unfold uc22pwI3dm
  fin_cases r <;> simp

theorem uc22pwI3_key_of_form (ν : MulAut (SpecialLinearGroup (Fin 3) K)) {A B : Matrix (Fin 3) (Fin 3) K}
    {i : ℕ} (hA : A.IsUpperTriangular) (hAB : A * B = 1)
    (hform : ∀ b : Kˣ, (ν (uc22pwI3dSL K b) : Matrix (Fin 3) (Fin 3) K) =
      A * uc22pwI3dm (b ^ 2 ^ i) * B) (a : Kˣ) :
    ν (uc22pwI3dSL K a) * (uc22pwI3dSL K (a ^ 2 ^ i))⁻¹ ∈ unitriangular 3 K := by
  rw [← map_inv]
  refine uc22pwI3_mem_unitriangular (A := A) (B := B) (D := uc22pwI3dm (a ^ 2 ^ i))
    (D' := uc22pwI3dm (a ^ 2 ^ i)⁻¹) hA (uc22pwI3dm_upper _) (uc22pwI3dm_upper _) hAB
    (uc22pwI3dm_diag _) ?_
  refine (Matrix.SpecialLinearGroup.coe_mul _ _).trans ?_
  rw [hform a]
  rfl

theorem uc22pwI3_key [Finite K] [CharP K 2] (ν : MulAut (SpecialLinearGroup (Fin 3) K))
    (hν : ∀ s, s ∈ unitriangular 3 K ↔ ν s ∈ unitriangular 3 K) :
    ∃ i : ℕ, ∀ a : Kˣ, ν (uc22pwI3dSL K a) * (uc22pwI3dSL K (a ^ 2 ^ i))⁻¹ ∈ unitriangular 3 K := by
  obtain ⟨A, φ, ε, hε, hνeq⟩ := CFSG.Quasithin.H13.Ch4.KGSL3.exists_standard ν
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow φ
  refine ⟨i, fun a => ?_⟩
  have hpre : ∀ u₁ ∈ unitriangular 3 K, ν.symm u₁ ∈ unitriangular 3 K ∧ ν (ν.symm u₁) = u₁ := by
    intro u₁ hu₁
    have h2 : ν (ν.symm u₁) = u₁ := ν.apply_symm_apply u₁
    exact ⟨(hν (ν.symm u₁)).2 (by rw [h2]; exact hu₁), h2⟩
  have hAB : (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    Units.mul_inv A
  have hBA : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 :=
    Units.inv_mul A
  interval_cases ε
  · have hmat : ∀ s : SpecialLinearGroup (Fin 3) K, (ν s : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) * (s : Matrix (Fin 3) (Fin 3) K).map φ *
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro s
      rw [hνeq]
      exact uc22pwI3_matrix_zero A φ s
    have hAup : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
      refine uc22pwI3_upper_of_invariant _ _ hAB hBA (fun u₁ hu₁ => ?_)
      obtain ⟨hs, hs'⟩ := hpre u₁ hu₁
      refine ⟨((ν.symm u₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ, ?_, ?_⟩
      · intro k l hkl
        simp [Matrix.map_apply, hs.1 k l hkl]
      · have h1 := hmat (ν.symm u₁)
        rw [hs'] at h1
        calc (u₁ : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)
            = ((A : Matrix (Fin 3) (Fin 3) K) *
              ((ν.symm u₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ *
                ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * (A : Matrix (Fin 3) (Fin 3) K) := by
              rw [← h1]
          _ = (A : Matrix (Fin 3) (Fin 3) K) *
              ((ν.symm u₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ := by
              rw [Matrix.mul_assoc, hBA, Matrix.mul_one]
    exact uc22pwI3_key_of_form ν hAup hAB (fun b => by
      rw [hmat, coe_uc22pwI3dSL, uc22pwI3_dm_map hi]) a
  · have hmat : ∀ s : SpecialLinearGroup (Fin 3) K, (ν s : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) *
          (((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ).map φ *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro s
      rw [hνeq]
      exact uc22pwI3_matrix_one A φ s
    have hJJ : uc22pwI3J K * uc22pwI3J K = 1 := uc22pwI3J_mul_self
    have hAB' : ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) *
        (uc22pwI3J K * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (uc22pwI3J K), hJJ, Matrix.one_mul, hAB]
    have hBA' : (uc22pwI3J K * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hBA,
        Matrix.one_mul, hJJ]
    have hAup : ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K).IsUpperTriangular := by
      refine uc22pwI3_upper_of_invariant _ _ hAB' hBA' (fun u₁ hu₁ => ?_)
      obtain ⟨hs, hs'⟩ := hpre u₁ hu₁
      refine ⟨uc22pwI3J K * ((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)ᵀ).map φ * uc22pwI3J K, ?_, ?_⟩
      · intro k l hkl
        rw [uc22pwI3J_conj]
        have hrev : (Fin.rev k) < Fin.rev l := Fin.rev_lt_rev.2 hkl
        have h0 := (inv_mem hs).1 (Fin.rev l) (Fin.rev k) hrev
        rw [Matrix.map_apply, Matrix.transpose_apply, h0, map_zero]
      · have h1 := hmat (ν.symm u₁)
        rw [hs'] at h1
        calc (u₁ : Matrix (Fin 3) (Fin 3) K) * ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K)
            = ((A : Matrix (Fin 3) (Fin 3) K) *
              (((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ).map φ) *
                ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
                  ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) := by rw [← h1]
          _ = ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) *
              (uc22pwI3J K * ((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K)ᵀ).map φ * uc22pwI3J K) := by
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hBA,
                Matrix.one_mul, ← Matrix.mul_assoc (uc22pwI3J K), hJJ, Matrix.one_mul]
    exact uc22pwI3_key_of_form ν hAup hAB' (fun b => by
      rw [hmat, uc22pwI3_graph_dm hi]
      simp only [Matrix.mul_assoc]) a

theorem coe_uc22pwI3Jsl [CharP K 2] :
    ((uc22pwI3Jsl K : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = uc22pwI3J K := rfl

theorem uc22pwI3Jsl_mul_self [CharP K 2] : uc22pwI3Jsl K * uc22pwI3Jsl K = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact congrFun (congrFun (uc22pwI3J_mul_self (K := K)) i) j

theorem uc22pwI3Jsl_sq [CharP K 2] : uc22pwI3Jsl K ^ 2 = 1 := by
  rw [pow_two]
  exact uc22pwI3Jsl_mul_self

theorem uc22pwI3Jsl_conj_dSL [CharP K 2] (a : Kˣ) :
    uc22pwI3Jsl K * uc22pwI3dSL K a * (uc22pwI3Jsl K)⁻¹ = (uc22pwI3dSL K a)⁻¹ := by
  have hinv : (uc22pwI3Jsl K)⁻¹ = uc22pwI3Jsl K := inv_eq_of_mul_eq_one_right uc22pwI3Jsl_mul_self
  rw [hinv, ← map_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show (uc22pwI3J K * uc22pwI3dm a * uc22pwI3J K) i j = uc22pwI3dm a⁻¹ i j
  rw [uc22pwI3J_conj]
  unfold uc22pwI3dm
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Fin.rev]

theorem uc22pwI3Jsl_not_mem_stabilizer [CharP K 2] {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ 2) :
    uc22pwI3Jsl K ∉ stabilizer (flagSpace 3 K i) := by
  intro h
  rw [mem_stabilizer] at h
  have he : (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) ∈ flagSpace 3 K i := by
    rw [mem_flagSpace]
    intro j hj
    have hj0 : j ≠ 0 := fun h0 => by
      rw [h0] at hj
      simp at hj
      omega
    exact Pi.single_eq_of_ne hj0 _
  have h1 : (uc22pwI3J K) *ᵥ (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) ∈ flagSpace 3 K i := by
    rw [← h]
    exact ⟨_, he, rfl⟩
  rw [mem_flagSpace] at h1
  have h2 := h1 2 (by simpa using hi2)
  simp [uc22pwI3J, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h2

theorem uc22pwI3_upper_sup_Jsl [CharP K 2] :
    upperTriangular 3 K ⊔ Subgroup.zpowers (uc22pwI3Jsl K) = ⊤ := by
  set A := upperTriangular 3 K ⊔ Subgroup.zpowers (uc22pwI3Jsl K) with hA
  have hBA : upperTriangular 3 K ≤ A := le_sup_left
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  have hcuts : borelOvergroupCuts A = ∅ := by
    by_contra hne
    obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hwA : uc22pwI3Jsl K ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [hAeq] at hwA
    have hw' := (mem_flagStabilizer.mp hwA) i hi
    obtain ⟨hi1, hin, -⟩ := hi
    exact uc22pwI3Jsl_not_mem_stabilizer hi1 (by omega) hw'
  rw [hcuts, flagStabilizer_empty] at hAeq
  exact hAeq

theorem uc22pwI3dSL_mem_upper (c : Kˣ) : uc22pwI3dSL K c ∈ upperTriangular 3 K :=
  mem_upperTriangular_iff_isUpperTriangular.2 (uc22pwI3dm_upper c)

theorem uc22pwI3dSL_eq_one_of_mem {c : Kˣ} (h : uc22pwI3dSL K c ∈ unitriangular 3 K) : c = 1 := by
  have h0 := h.2 0
  apply Units.ext
  simpa [coe_uc22pwI3dSL, uc22pwI3dm] using h0

theorem uc22pwI3_center_scalar {z : SpecialLinearGroup (Fin 3) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧ (z : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (c : K) := by
  have : z ∈ scalars 3 K := by
    rw [scalars_eq_center]
    exact hz
  exact this

theorem uc22pwI3_center_pow_three {z : SpecialLinearGroup (Fin 3) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) : z ^ 3 = 1 := by
  obtain ⟨c, hc, hzc⟩ := uc22pwI3_center_scalar hz
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow, hzc, ← map_pow, ← Units.val_pow_eq_pow_val, hc]
  simp

theorem uc22pwI3_dSL_eq_one_of_mul_center {c : Kˣ} {u z : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K))
    (h : uc22pwI3dSL K c = u * z) : c = 1 := by
  obtain ⟨d, -, hzd⟩ := uc22pwI3_center_scalar hz
  have h1 : ((uc22pwI3dSL K c : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 =
      ((u * z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 := by rw [h]
  rw [coe_uc22pwI3dSL, Matrix.SpecialLinearGroup.coe_mul, hzd] at h1
  have h2 : (d : K) = 1 := by
    have h3 := h1
    simp only [uc22pwI3dm, scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_apply_eq, hu.2 1,
      one_mul] at h3
    simpa using h3.symm
  have hd : d = 1 := Units.ext h2
  have hz1 : z = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hzd, hd, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]
  rw [hz1, mul_one] at h
  exact uc22pwI3dSL_eq_one_of_mem (h ▸ hu)

end CFSG.LocalAnalysis.UniquenessCase.UC22
