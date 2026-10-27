module

public import CFSG.RankThree.PartOne.K1320.L4Chain
public import CFSG.RankThree.PartOne.S12.InputsCT

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix
open Matrix.SpecialLinearGroup (transvection)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def emb3Mat (X : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks X 0 0 (1 : Matrix (Fin 1) (Fin 1) K))

omit [Finite K] [CharP K 2] in
theorem emb3Mat_mul (X Y : Matrix (Fin 3) (Fin 3) K) :
    emb3Mat (X * Y) = emb3Mat X * emb3Mat Y := by
  unfold emb3Mat
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

omit [Finite K] [CharP K 2] in
theorem emb3Mat_one : emb3Mat (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  unfold emb3Mat
  rw [Matrix.fromBlocks_one]
  simp

omit [Finite K] [CharP K 2] in
theorem emb3Mat_det (X : Matrix (Fin 3) (Fin 3) K) : (emb3Mat X).det = X.det := by
  unfold emb3Mat
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp

@[expose] noncomputable def emb3 (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun X := ⟨emb3Mat (X : Matrix (Fin 3) (Fin 3) K), by rw [emb3Mat_det, X.2]⟩
  map_one' := by
    apply Subtype.ext
    exact emb3Mat_one
  map_mul' X Y := by
    apply Subtype.ext
    exact emb3Mat_mul _ _

omit [Finite K] [CharP K 2] in
theorem coe_emb3 (X : Matrix.SpecialLinearGroup (Fin 3) K) :
    (emb3 K X : Matrix (Fin 4) (Fin 4) K) = emb3Mat (X : Matrix (Fin 3) (Fin 3) K) := rfl

omit [Finite K] [CharP K 2] in
theorem emb3Mat_apply (X : Matrix (Fin 3) (Fin 3) K) (a b : Fin 4) :
    emb3Mat X a b = if h : a.val < 3 ∧ b.val < 3 then X ⟨a, h.1⟩ ⟨b, h.2⟩
      else if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

omit [Finite K] [CharP K 2] in
theorem emb3_injective : Function.Injective (emb3 K) := by
  intro X Y h
  apply Subtype.ext
  ext a b
  have h1 := congrArg (fun Z : Matrix.SpecialLinearGroup (Fin 4) K =>
    (Z : Matrix (Fin 4) (Fin 4) K) ⟨a, by omega⟩ ⟨b, by omega⟩) h
  simpa [coe_emb3, emb3Mat_apply] using h1

omit [Finite K] [CharP K 2] in
theorem emb3_transvection {i j : Fin 3} (hij : i ≠ j) (c : K) :
    emb3 K (transvection hij c) =
      transvection (fun h => hij (Fin.castSucc_injective 3 h) :
        (i.castSucc : Fin 4) ≠ j.castSucc) c := by
  apply Subtype.ext
  ext a b
  rw [coe_emb3, emb3Mat_apply, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  by_cases h : a.val < 3 ∧ b.val < 3
  · simp only [h.1, h.2, and_self, ↓reduceDIte, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Fin.ext_iff, Fin.val_castSucc]
  · simp only [h, ↓reduceDIte]
    have hne : ¬ ((i.castSucc : Fin 4) = a ∧ (j.castSucc : Fin 4) = b) := by
      rintro ⟨h1, h2⟩
      apply h
      refine ⟨?_, ?_⟩
      · rw [← h1]
        simp
      · rw [← h2]
        simp
    simp [Matrix.add_apply, Matrix.one_apply, hne]

theorem eM_mem_pair {i j : Fin 3} (hij : i ≠ j) (c : K) :
    eM (fun h => hij (Fin.castSucc_injective 3 h) : (i.castSucc : Fin 4) ≠ j.castSucc) c ∈
      slB K 0 1 ⊔ slB K 1 2 := by
  set J := slB K 0 1 ⊔ slB K 1 2 with hJ
  have m01 : ∀ c : K, eM (by decide : (0 : Fin 4) ≠ 1) c ∈ J := fun c =>
    Subgroup.mem_sup_left (eM_mem_slB _ c)
  have m10 : ∀ c : K, eM (by decide : (1 : Fin 4) ≠ 0) c ∈ J := fun c =>
    Subgroup.mem_sup_left (eM_mem_slB_symm (by decide : (0 : Fin 4) ≠ 1) c)
  have m12 : ∀ c : K, eM (by decide : (1 : Fin 4) ≠ 2) c ∈ J := fun c =>
    Subgroup.mem_sup_right (eM_mem_slB _ c)
  have m21 : ∀ c : K, eM (by decide : (2 : Fin 4) ≠ 1) c ∈ J := fun c =>
    Subgroup.mem_sup_right (eM_mem_slB_symm (by decide : (1 : Fin 4) ≠ 2) c)
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact m01 c
  · have h := eM_mem_of_comm J (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 2) (m01 c) (m12 1)
    rwa [mul_one] at h
  · exact m10 c
  · exact absurd rfl hij
  · exact m12 c
  · have h := eM_mem_of_comm J (by decide : (2 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 0)
      (by decide : (2 : Fin 4) ≠ 0) (m21 c) (m10 1)
    rwa [mul_one] at h
  · exact m21 c
  · exact absurd rfl hij

theorem map_adSL_pair :
    (slB K 0 1 ⊔ slB K 1 2).map (adSL (K := K)).toMonoidHom = (emb3 K).range := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨h, c, rfl | rfl⟩
      · exact ⟨transvection (zero_ne_one : (0 : Fin 3) ≠ 1) c,
          (emb3_transvection _ c).trans (adSL_eM h c).symm⟩
      · exact ⟨transvection (one_ne_zero : (1 : Fin 3) ≠ 0) c,
          (emb3_transvection _ c).trans (adSL_eM h.symm c).symm⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨h, c, rfl | rfl⟩
      · exact ⟨transvection (by decide : (1 : Fin 3) ≠ 2) c,
          (emb3_transvection _ c).trans (adSL_eM h c).symm⟩
      · exact ⟨transvection (by decide : (2 : Fin 3) ≠ 1) c,
          (emb3_transvection _ c).trans (adSL_eM h.symm c).symm⟩
  · rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3)
      (K := K), MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, c, rfl⟩, rfl⟩
    refine ⟨eM (fun h => hij (Fin.castSucc_injective 3 h) : (i.castSucc : Fin 4) ≠ j.castSucc) c,
      eM_mem_pair hij c, ?_⟩
    exact (adSL_eM _ c).trans (emb3_transvection hij c).symm

@[expose] noncomputable def pairEquiv :
    ↥(slB K 0 1 ⊔ slB K 1 2) ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
  ((Subgroup.equivMapOfInjective _ (adSL (K := K)).toMonoidHom (adSL (K := K)).injective).trans
    (MulEquiv.subgroupCongr map_adSL_pair)).trans
    (MonoidHom.ofInjective (emb3_injective (K := K))).symm

theorem isSLModel_slB_pair {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CFSG.RankThree.PartOne.IsSLModelTwo 3 f ↥(slB K 0 1 ⊔ slB K 1 2) :=
  ⟨K, inferInstance, inferInstance, hK,
    ⟨pairEquiv.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)⟩⟩

end CFSG.RankThree.PartOne.K1320
