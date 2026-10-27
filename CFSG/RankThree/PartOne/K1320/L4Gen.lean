module

public import CFSG.RankThree.PartOne.K1320.L4Blocks

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix
open Matrix.SpecialLinearGroup (transvection)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_top_of_eM_mem (H : Subgroup ↥(M8 K))
    (h : ∀ {i j : Fin 4} (hij : i ≠ j) (c : K), eM hij c ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : adSL g ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 4 K) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top _
  have key : ∀ x ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 4 K),
      adSL.symm x ∈ H := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, j, hij, c, rfl⟩ := hx
      exact h hij c
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact H.mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact H.inv_mem hx
  simpa using key _ hg

theorem eM_conj_pM (σ : Equiv.Perm (Fin 4)) {i j : Fin 4} (h : i ≠ j) (h' : σ i ≠ σ j)
    (c : K) : pM σ * eM h c * (pM σ)⁻¹ = eM h' c := by
  apply adSL.injective
  rw [map_mul, map_mul, map_inv, adSL_pM, adSL_eM, adSL_eM]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext a b
  rw [psl_conj_apply, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  have e1 : (i = σ.symm a) ↔ (σ i = a) := Equiv.eq_symm_apply σ
  have e2 : (j = σ.symm b) ↔ (σ j = b) := Equiv.eq_symm_apply σ
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, e1, e2,
    (σ.symm).apply_eq_iff_eq]

omit [Finite K] in
theorem coe_psl_apply (σ : Equiv.Perm (Fin 4)) (k l : Fin 4) :
    ((psl σ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) k l =
      if k = σ l then 1 else 0 := by
  rw [coe_psl]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.symm_apply_eq]

theorem pM_apply_fvec (σ : Equiv.Perm (Fin 4)) (l : Fin 4) :
    ((pM σ : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l) = fvec K (σ l) := by
  rw [apply_fvec, adSL_pM]
  simp [coe_psl_apply]

@[expose] def sigS : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem sigS_zero : sigS 0 = 2 := by decide
theorem sigS_one : sigS 1 = 3 := by decide
theorem sigS_two : sigS 2 = 0 := by decide
theorem sigS_three : sigS 3 = 1 := by decide

theorem swapM_eq_pM : (swapM : ↥(M8 K)) = pM sigS := by
  apply eq_of_apply_fvec
  intro l
  rw [pM_apply_fvec]
  show (gSwap : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l) = _
  rw [gSwap_apply]
  fin_cases l
  · funext i
    fin_cases i <;> simp [fvec, fidx_symm_zero, fidx_symm_two, sigS_zero, ]
  · funext i
    fin_cases i <;> simp [fvec, fidx_symm_one, fidx_symm_three, sigS_one, ]
  · funext i
    fin_cases i <;> simp [fvec, fidx_symm_two, fidx_symm_zero, sigS_two, ]
  · funext i
    fin_cases i <;> simp [fvec, fidx_symm_three, fidx_symm_one, sigS_three, ]

@[expose] noncomputable def tauM (K : Type) [Field K] [Finite K] [CharP K 2] : ↥(M8 K) :=
  blk8M (transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : Qext K))

theorem adSL_tauM_coe :
    (adSL (tauM K) : Matrix (Fin 4) (Fin 4) K) =
      !![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1] := by
  apply adSL_eq_of_apply
  intro l
  fin_cases l
  · funext i
    fin_cases i <;> simp [tauM, blk8M_apply, fvec, fidx_symm_zero, Fin.sum_univ_four,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]
  · funext i
    fin_cases i <;> simp [tauM, blk8M_apply, fvec, fidx_symm_one, Fin.sum_univ_four,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]
  · funext i
    fin_cases i <;> simp [tauM, blk8M_apply, fvec, fidx_symm_zero, fidx_symm_two,
      Fin.sum_univ_four, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]
  · funext i
    fin_cases i <;> simp [tauM, blk8M_apply, fvec, fidx_symm_one, fidx_symm_three,
      Fin.sum_univ_four, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem adSL_tauM :
    adSL (tauM K) = transvection (by decide : (0 : Fin 4) ≠ 2) (1 : K) *
      transvection (by decide : (1 : Fin 4) ≠ 3) (1 : K) := by
  apply Subtype.ext
  rw [adSL_tauM_coe, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

omit [Finite K] [CharP K 2] in
theorem sl_comm_tau01 (c : K) :
    transvection (by decide : (0 : Fin 4) ≠ 1) c *
        (transvection (by decide : (0 : Fin 4) ≠ 2) (1 : K) *
          transvection (by decide : (1 : Fin 4) ≠ 3) (1 : K)) *
      (transvection (by decide : (0 : Fin 4) ≠ 1) c)⁻¹ *
        (transvection (by decide : (0 : Fin 4) ≠ 2) (1 : K) *
          transvection (by decide : (1 : Fin 4) ≠ 3) (1 : K))⁻¹ =
      transvection (by decide : (0 : Fin 4) ≠ 3) c := by
  set a := transvection (by decide : (0 : Fin 4) ≠ 1) c with ha
  set b := transvection (by decide : (0 : Fin 4) ≠ 2) (1 : K) with hb
  set b' := transvection (by decide : (1 : Fin 4) ≠ 3) (1 : K) with hb'
  set z := transvection (by decide : (0 : Fin 4) ≠ 3) c with hz
  have hab : a * b = b * a :=
    (Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide)
      (by decide) c 1).eq
  have hbz : b * z = z * b :=
    (Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide)
      (by decide) 1 c).eq
  have hcomm : a * b' = z * b' * a := by
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 3) (by decide : (0 : Fin 4) ≠ 3)
      c (1 : K)
    rw [commutatorElement_def, mul_one] at h
    calc a * b' = (a * b' * a⁻¹ * b'⁻¹) * b' * a := by group
      _ = z * b' * a := by rw [h]
  have h1 : a * (b * b') = z * (b * b') * a := by
    calc a * (b * b') = (a * b) * b' := by group
      _ = (b * a) * b' := by rw [hab]
      _ = b * (a * b') := by group
      _ = b * (z * b' * a) := by rw [hcomm]
      _ = (b * z) * b' * a := by group
      _ = (z * b) * b' * a := by rw [hbz]
      _ = z * (b * b') * a := by group
  rw [h1]
  group

omit [Finite K] [CharP K 2] in
theorem sl_comm_tau10 (c : K) :
    transvection (by decide : (1 : Fin 4) ≠ 0) c *
        (transvection (by decide : (0 : Fin 4) ≠ 2) (1 : K) *
          transvection (by decide : (1 : Fin 4) ≠ 3) (1 : K)) *
      (transvection (by decide : (1 : Fin 4) ≠ 0) c)⁻¹ *
        (transvection (by decide : (0 : Fin 4) ≠ 2) (1 : K) *
          transvection (by decide : (1 : Fin 4) ≠ 3) (1 : K))⁻¹ =
      transvection (by decide : (1 : Fin 4) ≠ 2) c := by
  set a := transvection (by decide : (1 : Fin 4) ≠ 0) c with ha
  set b := transvection (by decide : (0 : Fin 4) ≠ 2) (1 : K) with hb
  set b' := transvection (by decide : (1 : Fin 4) ≠ 3) (1 : K) with hb'
  set z := transvection (by decide : (1 : Fin 4) ≠ 2) c with hz
  have hab' : a * b' = b' * a :=
    (Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide)
      (by decide) c 1).eq
  have hcomm : a * b = z * b * a := by
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (by decide : (1 : Fin 4) ≠ 0) (by decide : (0 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 2)
      c (1 : K)
    rw [commutatorElement_def, mul_one] at h
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = z * b * a := by rw [h]
  have h1 : a * (b * b') = z * (b * b') * a := by
    calc a * (b * b') = (a * b) * b' := by group
      _ = (z * b * a) * b' := by rw [hcomm]
      _ = z * b * (a * b') := by group
      _ = z * b * (b' * a) := by rw [hab']
      _ = z * (b * b') * a := by group
  rw [h1]
  group

theorem comm_eM01_tauM (c : K) :
    eM (by decide : (0 : Fin 4) ≠ 1) c * tauM K * (eM (by decide : (0 : Fin 4) ≠ 1) c)⁻¹ *
      (tauM K)⁻¹ = eM (by decide : (0 : Fin 4) ≠ 3) c := by
  apply adSL.injective
  simp only [map_mul, map_inv, adSL_eM, adSL_tauM]
  exact sl_comm_tau01 c

theorem comm_eM10_tauM (c : K) :
    eM (by decide : (1 : Fin 4) ≠ 0) c * tauM K * (eM (by decide : (1 : Fin 4) ≠ 0) c)⁻¹ *
      (tauM K)⁻¹ = eM (by decide : (1 : Fin 4) ≠ 2) c := by
  apply adSL.injective
  simp only [map_mul, map_inv, adSL_eM, adSL_tauM]
  exact sl_comm_tau10 c

theorem comm_eM {i j l : Fin 4} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (c d : K) :
    eM hij c * eM hjl d * (eM hij c)⁻¹ * (eM hjl d)⁻¹ = eM hil (c * d) := by
  apply adSL.injective
  simp only [map_mul, map_inv, adSL_eM]
  exact Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil c d

theorem blkA_zero_sup_blk8M (_h4 : 4 ≤ Nat.card K) :
    (blkA (K := K) 0).range ⊔ (blk8M (K := K)).range = ⊤ := by
  set H := (blkA (K := K) 0).range ⊔ (blk8M (K := K)).range with hH
  have m01 : ∀ c : K, eM (by decide : (0 : Fin 4) ≠ 1) c ∈ H := fun c =>
    Subgroup.mem_sup_left ⟨_, blkA_zero_trU c⟩
  have m10 : ∀ c : K, eM (by decide : (1 : Fin 4) ≠ 0) c ∈ H := fun c =>
    Subgroup.mem_sup_left ⟨_, blkA_zero_trL c⟩
  have hτ : tauM K ∈ H := Subgroup.mem_sup_right ⟨_, rfl⟩
  have hw : (pM sigS : ↥(M8 K)) ∈ H := by
    rw [← swapM_eq_pM]
    exact Subgroup.mem_sup_right ⟨wSL2, swapM_eq_blk8M.symm⟩
  have conj : ∀ {i j i' j' : Fin 4} (h : i ≠ j) (h' : i' ≠ j') (hi : sigS i = i')
      (hj : sigS j = j') (c : K), eM h c ∈ H → eM h' c ∈ H := by
    intro i j i' j' h h' hi hj c hm
    subst hi
    subst hj
    rw [← eM_conj_pM sigS h h' c]
    exact H.mul_mem (H.mul_mem hw hm) (H.inv_mem hw)
  have m03 : ∀ c : K, eM (by decide : (0 : Fin 4) ≠ 3) c ∈ H := fun c => by
    rw [← comm_eM01_tauM c]
    exact H.mul_mem (H.mul_mem (H.mul_mem (m01 c) hτ) (H.inv_mem (m01 c))) (H.inv_mem hτ)
  have m12 : ∀ c : K, eM (by decide : (1 : Fin 4) ≠ 2) c ∈ H := fun c => by
    rw [← comm_eM10_tauM c]
    exact H.mul_mem (H.mul_mem (H.mul_mem (m10 c) hτ) (H.inv_mem (m10 c))) (H.inv_mem hτ)
  have m23 : ∀ c : K, eM (by decide : (2 : Fin 4) ≠ 3) c ∈ H := fun c =>
    conj (by decide) (by decide) sigS_zero sigS_one c (m01 c)
  have m32 : ∀ c : K, eM (by decide : (3 : Fin 4) ≠ 2) c ∈ H := fun c =>
    conj (by decide) (by decide) sigS_one sigS_zero c (m10 c)
  have m21 : ∀ c : K, eM (by decide : (2 : Fin 4) ≠ 1) c ∈ H := fun c =>
    conj (by decide) (by decide) sigS_zero sigS_three c (m03 c)
  have m30 : ∀ c : K, eM (by decide : (3 : Fin 4) ≠ 0) c ∈ H := fun c =>
    conj (by decide) (by decide) sigS_one sigS_two c (m12 c)
  have m02 : ∀ c : K, eM (by decide : (0 : Fin 4) ≠ 2) c ∈ H := fun c => by
    have h := comm_eM (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 2) c 1
    rw [mul_one] at h
    rw [← h]
    exact H.mul_mem (H.mul_mem (H.mul_mem (m01 c) (m12 1)) (H.inv_mem (m01 c)))
      (H.inv_mem (m12 1))
  have m13 : ∀ c : K, eM (by decide : (1 : Fin 4) ≠ 3) c ∈ H := fun c => by
    have h := comm_eM (by decide : (1 : Fin 4) ≠ 2) (by decide : (2 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 3) c 1
    rw [mul_one] at h
    rw [← h]
    exact H.mul_mem (H.mul_mem (H.mul_mem (m12 c) (m23 1)) (H.inv_mem (m12 c)))
      (H.inv_mem (m23 1))
  have m20 : ∀ c : K, eM (by decide : (2 : Fin 4) ≠ 0) c ∈ H := fun c =>
    conj (by decide) (by decide) sigS_zero sigS_two c (m02 c)
  have m31 : ∀ c : K, eM (by decide : (3 : Fin 4) ≠ 1) c ∈ H := fun c =>
    conj (by decide) (by decide) sigS_one sigS_three c (m13 c)
  refine eq_top_of_eM_mem H fun {i j} hij c => ?_
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact m01 c
  · exact m02 c
  · exact m03 c
  · exact m10 c
  · exact absurd rfl hij
  · exact m12 c
  · exact m13 c
  · exact m20 c
  · exact m21 c
  · exact absurd rfl hij
  · exact m23 c
  · exact m30 c
  · exact m31 c
  · exact m32 c
  · exact absurd rfl hij

end CFSG.RankThree.PartOne.K1320
