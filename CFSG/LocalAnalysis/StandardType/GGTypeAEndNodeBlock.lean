module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeAFrame

public section

namespace CFSG.StandardType

open Matrix

section Upper

variable (n : ℕ) (F : Type) [Field F]

@[expose] noncomputable def slUpperBlockMat (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) F))

variable {n F}

theorem slUpperBlockMat_apply (A : Matrix (Fin n) (Fin n) F) (p q : Fin n ⊕ Fin 1) :
    slUpperBlockMat n F A (finSumFinEquiv p) (finSumFinEquiv q) =
      Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) F) p q := by
  simp [slUpperBlockMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem slUpperBlockMat_mul (A B : Matrix (Fin n) (Fin n) F) :
    slUpperBlockMat n F (A * B) = slUpperBlockMat n F A * slUpperBlockMat n F B := by
  rw [slUpperBlockMat, slUpperBlockMat, slUpperBlockMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem slUpperBlockMat_one : slUpperBlockMat n F (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [slUpperBlockMat, Matrix.fromBlocks_one, map_one]

theorem det_slUpperBlockMat (A : Matrix (Fin n) (Fin n) F) :
    (slUpperBlockMat n F A).det = A.det := by
  rw [slUpperBlockMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    mul_one]

theorem slUpperBlockMat_injective : Function.Injective (slUpperBlockMat n F) := fun A B h => by
  have h' := (Matrix.reindexAlgEquiv F F (finSumFinEquiv (m := n) (n := 1))).injective h
  exact (Matrix.fromBlocks_inj.1 h').1

theorem slUpperBlockMat_transpose (A : Matrix (Fin n) (Fin n) F) :
    (slUpperBlockMat n F A).transpose = slUpperBlockMat n F A.transpose := by
  ext a b
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective b
  rw [Matrix.transpose_apply, slUpperBlockMat_apply, slUpperBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply, eq_comm]

theorem slUpperBlockMat_map {f : F → F} (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (A : Matrix (Fin n) (Fin n) F) :
    (slUpperBlockMat n F A).map f = slUpperBlockMat n F (A.map f) := by
  ext a b
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective b
  rw [Matrix.map_apply, slUpperBlockMat_apply, slUpperBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply, apply_ite f, hf0, hf1]

variable (n F) in
@[expose] noncomputable def slUpperBlockMonoidHom :
    Matrix (Fin n) (Fin n) F →* Matrix (Fin (n + 1)) (Fin (n + 1)) F where
  toFun := slUpperBlockMat n F
  map_one' := slUpperBlockMat_one
  map_mul' := slUpperBlockMat_mul

variable (n F) in
@[expose] noncomputable def slUpperBlockHom :
    Matrix.SpecialLinearGroup (Fin n) F →* Matrix.SpecialLinearGroup (Fin (n + 1)) F where
  toFun A := ⟨slUpperBlockMat n F (A : Matrix (Fin n) (Fin n) F),
    by rw [det_slUpperBlockMat]; exact A.2⟩
  map_one' := Subtype.ext (by
    change slUpperBlockMat n F ((1 : Matrix.SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, slUpperBlockMat_one])
  map_mul' A B := Subtype.ext (by
    change slUpperBlockMat n F ((A * B : Matrix.SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) =
      slUpperBlockMat n F (A : Matrix (Fin n) (Fin n) F) *
        slUpperBlockMat n F (B : Matrix (Fin n) (Fin n) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, slUpperBlockMat_mul])

theorem coe_slUpperBlockHom (A : Matrix.SpecialLinearGroup (Fin n) F) :
    ((slUpperBlockHom n F A : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) = slUpperBlockMat n F (A : Matrix (Fin n) (Fin n) F) :=
  rfl

theorem slUpperBlockHom_injective : Function.Injective (slUpperBlockHom n F) := fun _ _ h =>
  Subtype.ext (slUpperBlockMat_injective (congrArg Subtype.val h))

theorem slBlock_castAdd_one_eq (p : Fin n) : (Fin.castAdd 1 p : Fin (n + 1)) = p.castSucc := rfl

theorem slBlock_natAdd_zero_eq_last : (Fin.natAdd n (0 : Fin 1) : Fin (n + 1)) = Fin.last n :=
  Fin.ext (by simp)

theorem slUpperBlockHom_transvection {i j : Fin n} (hij : i ≠ j) (c : F) :
    slUpperBlockHom n F (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection ((Fin.castSucc_injective _).ne hij) c := by
  apply Subtype.ext
  rw [coe_slUpperBlockHom]
  ext a b
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective b
  rw [slUpperBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q
  · simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
      slBlock_castAdd_one_eq]
  · obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [Matrix.SpecialLinearGroup.transvection_coe, slBlock_castAdd_one_eq,
      slBlock_natAdd_zero_eq_last, Fin.castSucc_ne_last]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    simp [Matrix.SpecialLinearGroup.transvection_coe, slBlock_castAdd_one_eq,
      slBlock_natAdd_zero_eq_last, (Fin.castSucc_ne_last _).symm]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [Matrix.SpecialLinearGroup.transvection_coe, slBlock_natAdd_zero_eq_last]

theorem eq_one_of_slUpperBlockHom_mem_center {g : Matrix.SpecialLinearGroup (Fin n) F}
    (h : slUpperBlockHom n F g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) F)) :
    g = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  have hlast := congrFun (congrFun hr (Fin.last n)) (Fin.last n)
  rw [coe_slUpperBlockHom, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    ← slBlock_natAdd_zero_eq_last,
    ← finSumFinEquiv_apply_right, slUpperBlockMat_apply] at hlast
  simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq] at hlast
  apply slUpperBlockHom_injective
  rw [map_one]
  apply Subtype.ext
  rw [← hr, hlast, Matrix.SpecialLinearGroup.coe_one]
  simp

end Upper

section Lower

variable (n : ℕ) (F : Type) [Field F]

@[expose] def slLowerBlockEquiv : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))

variable {n} in
theorem slLowerBlockEquiv_inl (p : Fin 1) : slLowerBlockEquiv n (Sum.inl p) = 0 := by
  ext
  simp [slLowerBlockEquiv]

variable {n} in
theorem slLowerBlockEquiv_inr (i : Fin n) : slLowerBlockEquiv n (Sum.inr i) = i.succ := by
  ext
  simp [slLowerBlockEquiv]

@[expose] noncomputable def slLowerBlockMat (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.reindexAlgEquiv F F (slLowerBlockEquiv n)
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0 A)

variable {n F}

theorem slLowerBlockMat_apply (A : Matrix (Fin n) (Fin n) F) (p q : Fin 1 ⊕ Fin n) :
    slLowerBlockMat n F A (slLowerBlockEquiv n p) (slLowerBlockEquiv n q) =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0 A p q := by
  simp [slLowerBlockMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem slLowerBlockMat_mul (A B : Matrix (Fin n) (Fin n) F) :
    slLowerBlockMat n F (A * B) = slLowerBlockMat n F A * slLowerBlockMat n F B := by
  rw [slLowerBlockMat, slLowerBlockMat, slLowerBlockMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem slLowerBlockMat_one : slLowerBlockMat n F (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [slLowerBlockMat, Matrix.fromBlocks_one, map_one]

theorem det_slLowerBlockMat (A : Matrix (Fin n) (Fin n) F) :
    (slLowerBlockMat n F A).det = A.det := by
  rw [slLowerBlockMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    one_mul]

theorem slLowerBlockMat_injective : Function.Injective (slLowerBlockMat n F) := fun A B h => by
  have h' := (Matrix.reindexAlgEquiv F F (slLowerBlockEquiv n)).injective h
  exact (Matrix.fromBlocks_inj.1 h').2.2.2

variable (n F) in
@[expose] noncomputable def slLowerBlockHom :
    Matrix.SpecialLinearGroup (Fin n) F →* Matrix.SpecialLinearGroup (Fin (n + 1)) F where
  toFun A := ⟨slLowerBlockMat n F (A : Matrix (Fin n) (Fin n) F),
    by rw [det_slLowerBlockMat]; exact A.2⟩
  map_one' := Subtype.ext (by
    change slLowerBlockMat n F ((1 : Matrix.SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, slLowerBlockMat_one])
  map_mul' A B := Subtype.ext (by
    change slLowerBlockMat n F ((A * B : Matrix.SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) =
      slLowerBlockMat n F (A : Matrix (Fin n) (Fin n) F) *
        slLowerBlockMat n F (B : Matrix (Fin n) (Fin n) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, slLowerBlockMat_mul])

theorem coe_slLowerBlockHom (A : Matrix.SpecialLinearGroup (Fin n) F) :
    ((slLowerBlockHom n F A : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) = slLowerBlockMat n F (A : Matrix (Fin n) (Fin n) F) :=
  rfl

theorem slLowerBlockHom_injective : Function.Injective (slLowerBlockHom n F) := fun _ _ h =>
  Subtype.ext (slLowerBlockMat_injective (congrArg Subtype.val h))

theorem slLowerBlockHom_transvection {i j : Fin n} (hij : i ≠ j) (c : F) :
    slLowerBlockHom n F (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection ((Fin.succ_injective _).ne hij) c := by
  apply Subtype.ext
  rw [coe_slLowerBlockHom]
  ext a b
  obtain ⟨p, rfl⟩ := (slLowerBlockEquiv n).surjective a
  obtain ⟨q, rfl⟩ := (slLowerBlockEquiv n).surjective b
  rw [slLowerBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [Matrix.SpecialLinearGroup.transvection_coe, slLowerBlockEquiv_inl, Fin.succ_ne_zero]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    simp [Matrix.SpecialLinearGroup.transvection_coe, slLowerBlockEquiv_inl, slLowerBlockEquiv_inr,
      (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]
  · obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [Matrix.SpecialLinearGroup.transvection_coe, slLowerBlockEquiv_inl, slLowerBlockEquiv_inr,
      Fin.succ_ne_zero]
  · simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
      slLowerBlockEquiv_inr]

theorem eq_one_of_slLowerBlockHom_mem_center {g : Matrix.SpecialLinearGroup (Fin n) F}
    (h : slLowerBlockHom n F g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) F)) :
    g = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  have h0 := congrFun (congrFun hr 0) 0
  rw [coe_slLowerBlockHom, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    ← slLowerBlockEquiv_inl (n := n) 0, slLowerBlockMat_apply] at h0
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply_eq] at h0
  apply slLowerBlockHom_injective
  rw [map_one]
  apply Subtype.ext
  rw [← hr, h0, Matrix.SpecialLinearGroup.coe_one]
  simp

end Lower

end CFSG.StandardType
