module

public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Rep
public import CFSG.ClassicalGroups.Alternating.Generation

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBN

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
  CFSG.ClassicalGroups.Alternating

variable {K : Type} [Field K]

variable (K) in
@[expose] def f4B2Form : LinearMap.BilinForm K (Fin 4 → K) :=
  Matrix.toBilin' (f4J0 K)

theorem f4B2Form_apply (x y : Fin 4 → K) : f4B2Form K x y = x ⬝ᵥ (f4J0 K *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem f4B2Form_isAlt : (f4B2Form K).IsAlt := fun x => by
  rw [f4B2Form_apply]
  simp [f4J0, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

theorem det_f4J0 : (f4J0 K).det = 1 := by
  simp [f4J0, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

theorem f4B2Form_nondegenerate : (f4B2Form K).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ (by rw [det_f4J0]; exact one_ne_zero)

theorem mem_matrixIsometryGroup_f4J0_iff {A : GL (Fin 4) K} :
    A ∈ matrixIsometryGroup (f4J0 K) ↔
      Matrix.GeneralLinearGroup.toLin A ∈ bilinIsometryGroup (f4B2Form K) := by
  rw [mem_matrixIsometryGroup, mem_bilinIsometryGroup]
  have e : ∀ x y, f4B2Form K ((Matrix.GeneralLinearGroup.toLin A : (Fin 4 → K) →ₗ[K] Fin 4 → K) x)
      ((Matrix.GeneralLinearGroup.toLin A : (Fin 4 → K) →ₗ[K] Fin 4 → K) y) =
      Matrix.toBilin' ((A : Matrix (Fin 4) (Fin 4) K)ᵀ * f4J0 K * (A : Matrix (Fin 4) (Fin 4) K))
        x y := fun x y => by
    rw [← Matrix.toBilin'_comp]
    rfl
  simp only [e]
  constructor
  · intro h x y
    rw [h]
    rfl
  · intro h
    apply Matrix.toBilin'.injective
    exact LinearMap.ext fun x => LinearMap.ext fun y => h x y

@[expose] def f4TransMat (a : Fin 4 → K) (c : K) : Matrix (Fin 4) (Fin 4) K :=
  1 + c • vecMulVec a (f4J0 K *ᵥ a)

theorem f4TransMat_mulVec (a : Fin 4 → K) (c : K) (x : Fin 4 → K) :
    f4TransMat a c *ᵥ x = x + (c * f4B2Form K x a) • a := by
  rw [f4TransMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec,
    f4B2Form_apply, dotProduct_comm, op_smul_eq_smul, smul_smul]

theorem gl_ext_mulVec' {g h : GL (Fin 4) K}
    (H : ∀ x, (g : Matrix (Fin 4) (Fin 4) K) *ᵥ x = (h : Matrix (Fin 4) (Fin 4) K) *ᵥ x) :
    g = h :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, H]))

theorem f4TransMat_mul (a : Fin 4 → K) (c d : K) :
    f4TransMat a c * f4TransMat a d = f4TransMat a (c + d) := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, f4TransMat_mulVec, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, f4B2Form_isAlt a, smul_eq_mul, mul_zero, add_zero]
  rw [add_assoc, ← add_smul]
  congr 2
  ring

theorem f4TransMat_zero (a : Fin 4 → K) : f4TransMat a 0 = 1 := by
  rw [f4TransMat, zero_smul, add_zero]

@[expose] def f4Trans (a : Fin 4 → K) (c : K) : GL (Fin 4) K where
  val := f4TransMat a c
  inv := f4TransMat a (-c)
  val_inv := by rw [f4TransMat_mul, add_neg_cancel, f4TransMat_zero]
  inv_val := by rw [f4TransMat_mul, neg_add_cancel, f4TransMat_zero]

theorem f4Trans_mulVec (a : Fin 4 → K) (c : K) (x : Fin 4 → K) :
    ((f4Trans a c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x =
      x + (c * f4B2Form K x a) • a :=
  f4TransMat_mulVec a c x

theorem f4Trans_zero_vec (c : K) : f4Trans (0 : Fin 4 → K) c = 1 :=
  gl_ext_mulVec' fun x => by rw [f4Trans_mulVec, smul_zero, add_zero, Units.val_one, one_mulVec]

theorem f4Trans_smul (a : Fin 4 → K) (l c : K) : f4Trans (l • a) c = f4Trans a (l ^ 2 * c) :=
  gl_ext_mulVec' fun x => by
    rw [f4Trans_mulVec, f4Trans_mulVec, map_smul, smul_eq_mul, smul_smul]
    congr 2
    ring

theorem gl_mulVec_inv_mulVec' (g : GL (Fin 4) K) (x : Fin 4 → K) :
    (g : Matrix (Fin 4) (Fin 4) K) *ᵥ (((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x) =
      x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem f4B2Form_mulVec {g : GL (Fin 4) K} (hg : g ∈ matrixIsometryGroup (f4J0 K))
    (x y : Fin 4 → K) :
    f4B2Form K ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ x) ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ y) =
      f4B2Form K x y := by
  have h := mem_matrixIsometryGroup_f4J0_iff.1 hg x y
  simpa [Matrix.GeneralLinearGroup.coe_toLin] using h

theorem conj_f4Trans {g : GL (Fin 4) K} (hg : g ∈ matrixIsometryGroup (f4J0 K))
    (a : Fin 4 → K) (c : K) :
    g * f4Trans a c * g⁻¹ = f4Trans ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ a) c :=
  gl_ext_mulVec' fun x => by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      f4Trans_mulVec, f4Trans_mulVec, mulVec_add, mulVec_smul, gl_mulVec_inv_mulVec']
    congr 3
    rw [← f4B2Form_mulVec hg, gl_mulVec_inv_mulVec']

theorem f4Trans_mem (a : Fin 4 → K) (c : K) : f4Trans a c ∈ matrixIsometryGroup (f4J0 K) := by
  rw [mem_matrixIsometryGroup_f4J0_iff, mem_bilinIsometryGroup]
  intro x y
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, f4Trans_mulVec,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, f4B2Form_isAlt a]
  have hs : f4B2Form K a y = -f4B2Form K y a := by
    rw [← LinearMap.BilinForm.IsAlt.neg_eq f4B2Form_isAlt]
  rw [hs]
  ring

theorem matrixIsometryGroup_f4J0_eq_closure :
    matrixIsometryGroup (f4J0 K) =
      Subgroup.closure {g | ∃ (a : Fin 4 → K) (c : K), g = f4Trans a c} := by
  refine le_antisymm (fun A hA => ?_) ((Subgroup.closure_le _).mpr ?_)
  · have h := mem_matrixIsometryGroup_f4J0_iff.mp hA
    rw [alternating_transvection_generation f4B2Form_isAlt f4B2Form_nondegenerate] at h
    have h' := Subgroup.mem_map_of_mem
      (Matrix.GeneralLinearGroup.toLin (n := Fin 4) (R := K)).symm.toMonoidHom h
    rw [MonoidHom.map_closure] at h'
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h'
    refine Subgroup.closure_mono ?_ h'
    rintro _ ⟨_, ⟨a, c, rfl⟩, rfl⟩
    refine ⟨a, c, ?_⟩
    apply (Matrix.GeneralLinearGroup.toLin (n := Fin 4) (R := K)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    refine LinearMap.ext fun x => ?_
    rw [symplecticTransvection_apply, Matrix.GeneralLinearGroup.coe_toLin,
      Matrix.mulVecLin_apply, f4Trans_mulVec]
  · rintro _ ⟨a, c, rfl⟩
    exact f4Trans_mem a c

variable (K) in
abbrev f4B2Image
    : Subgroup (GL (Fin 4) K) :=
  (f4B2Rep K).range.map (matrixIsometryGroup (f4J0 K)).subtype

theorem f4B2Image_le
    : f4B2Image K ≤ matrixIsometryGroup (f4J0 K) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem f4B2Rep_mem_image
    (g : subsystemGroup Tag.F4 K {1, 2}) :
    ((f4B2Rep K g : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) ∈ f4B2Image K :=
  ⟨_, ⟨g, rfl⟩, rfl⟩

theorem exists_image_x1 (c : K) :
    ∃ h ∈ f4B2Image K, (h : Matrix (Fin 4) (Fin 4) K) = 1 + single 1 2 c :=
  ⟨_, f4B2Rep_mem_image (qx (left_mem_pair 1 2) c), by
    rw [coe_f4B2Rep, coe_qx, f4B2BlockMat_x1]⟩

theorem exists_image_y1 (c : K) :
    ∃ h ∈ f4B2Image K, (h : Matrix (Fin 4) (Fin 4) K) = 1 + single 2 1 c :=
  ⟨_, f4B2Rep_mem_image (qy (left_mem_pair 1 2) c), by
    rw [coe_f4B2Rep, coe_qy, f4B2BlockMat_y1]⟩

theorem exists_image_x2 (c : K) :
    ∃ h ∈ f4B2Image K, (h : Matrix (Fin 4) (Fin 4) K) = 1 + single 0 1 c + single 2 3 c :=
  ⟨_, f4B2Rep_mem_image (qx (right_mem_pair 1 2) c), by
    rw [coe_f4B2Rep, coe_qx, f4B2BlockMat_x2]⟩

theorem exists_image_y2 (c : K) :
    ∃ h ∈ f4B2Image K, (h : Matrix (Fin 4) (Fin 4) K) = 1 + single 1 0 c + single 3 2 c :=
  ⟨_, f4B2Rep_mem_image (qy (right_mem_pair 1 2) c), by
    rw [coe_f4B2Rep, coe_qy, f4B2BlockMat_y2]⟩

theorem one_add_single_mulVec (i j : Fin 4) (c : K) (v : Fin 4 → K) :
    (1 + single i j c : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v + Pi.single i (c * v j) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq, ← Pi.single_smul, smul_eq_mul,
    mul_one]

theorem one_add_single_add_single_mulVec (i j k l : Fin 4) (c : K) (v : Fin 4 → K) :
    (1 + single i j c + single k l c : Matrix (Fin 4) (Fin 4) K) *ᵥ v =
      v + Pi.single i (c * v j) + Pi.single k (c * v l) := by
  rw [Matrix.add_mulVec, one_add_single_mulVec, single_mulVec_eq, ← Pi.single_smul, smul_eq_mul,
    mul_one]

@[expose] def OrbitE1
    (v : Fin 4 → K) : Prop :=
  ∃ h ∈ f4B2Image K, ∃ l : K, l ≠ 0 ∧ (h : Matrix (Fin 4) (Fin 4) K) *ᵥ v = l • Pi.single 1 1

theorem OrbitE1.of_mulVec
    {g : GL (Fin 4) K} (hg : g ∈ f4B2Image K) {v : Fin 4 → K}
    (h : OrbitE1 ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ v)) : OrbitE1 v := by
  obtain ⟨h', hh', l, hl, e⟩ := h
  exact ⟨h' * g, mul_mem hh' hg, l, hl, by rw [Units.val_mul, ← Matrix.mulVec_mulVec, e]⟩

theorem orbitE1_of_one_ne_zero
    {v : Fin 4 → K} (hv1 : v 1 ≠ 0) : OrbitE1 v := by
  obtain ⟨A₁, hA₁, eA₁⟩ := exists_image_x2 (K := K) (-(v 0 / v 1))
  refine OrbitE1.of_mulVec hA₁ ?_
  rw [eA₁, one_add_single_add_single_mulVec]
  set w := v + Pi.single 0 (-(v 0 / v 1) * v 1) + Pi.single 2 (-(v 0 / v 1) * v 3) with hw
  have w1 : w 1 = v 1 := by simp [hw]
  obtain ⟨A₂, hA₂, eA₂⟩ := exists_image_y1 (K := K) (-(w 2 / v 1))
  obtain ⟨A₃, hA₃, eA₃⟩ := exists_image_y1 (K := K) 1
  obtain ⟨A₄, hA₄, eA₄⟩ := exists_image_y2 (K := K) (-(w 3 / v 1))
  obtain ⟨A₅, hA₅, eA₅⟩ := exists_image_y1 (K := K) (-1)
  refine ⟨A₅ * A₄ * A₃ * A₂, mul_mem (mul_mem (mul_mem hA₅ hA₄) hA₃) hA₂, v 1, hv1, ?_⟩
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, eA₂, eA₃, eA₄, eA₅, one_add_single_mulVec,
    one_add_single_add_single_mulVec]
  have w0 : w 0 = 0 := by simp [hw, hv1]
  funext k
  fin_cases k <;> simp [w0, w1] <;> field_simp <;> ring

theorem orbitE1_of_ne_zero
    {v : Fin 4 → K} (hv : v ≠ 0) : OrbitE1 v := by
  by_cases h1 : v 1 = 0
  · by_cases h2 : v 2 = 0
    · by_cases h0 : v 0 = 0
      · have h3 : v 3 ≠ 0 := fun h3 => hv (funext fun k => by fin_cases k <;> assumption)
        obtain ⟨A, hA, eA⟩ := exists_image_x2 (K := K) 1
        obtain ⟨B, hB, eB⟩ := exists_image_x1 (K := K) 1
        refine OrbitE1.of_mulVec hA (OrbitE1.of_mulVec hB (orbitE1_of_one_ne_zero ?_))
        rw [eA, eB, one_add_single_add_single_mulVec, one_add_single_mulVec]
        simp [h1, h2, h3]
      · obtain ⟨A, hA, eA⟩ := exists_image_y2 (K := K) 1
        refine OrbitE1.of_mulVec hA (orbitE1_of_one_ne_zero ?_)
        rw [eA, one_add_single_add_single_mulVec]
        simp [h1, h0]
    · obtain ⟨A, hA, eA⟩ := exists_image_x1 (K := K) 1
      refine OrbitE1.of_mulVec hA (orbitE1_of_one_ne_zero ?_)
      rw [eA, one_add_single_mulVec]
      simp [h1, h2]
  · exact orbitE1_of_one_ne_zero h1

theorem f4Trans_single_one (c : K) :
    ((f4Trans (Pi.single 1 1) c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 + single 1 2 c := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, f4Trans_mulVec, one_add_single_mulVec,
    f4B2Form_apply]
  simp [f4J0, dotProduct, Matrix.mulVec, Fin.sum_univ_four, ← Pi.single_smul]

theorem f4Trans_mem_image
    (a : Fin 4 → K) (c : K) : f4Trans a c ∈ f4B2Image K := by
  by_cases ha : a = 0
  · subst ha
    rw [f4Trans_zero_vec]
    exact one_mem _
  obtain ⟨h, hh, l, -, e⟩ := orbitE1_of_ne_zero ha
  have hsp : h⁻¹ ∈ matrixIsometryGroup (f4J0 K) := f4B2Image_le (inv_mem hh)
  have ha' : a = ((h⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (l • Pi.single 1 1) := by
    rw [← e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hT : f4Trans (Pi.single 1 1) (l ^ 2 * c) ∈ f4B2Image K := by
    obtain ⟨X, hX, eX⟩ := exists_image_x1 (K := K) (l ^ 2 * c)
    have hXe : X = f4Trans (Pi.single 1 1) (l ^ 2 * c) :=
      Units.ext (eX.trans (f4Trans_single_one _).symm)
    rw [← hXe]
    exact hX
  rw [ha', ← conj_f4Trans hsp, f4Trans_smul]
  exact mul_mem (mul_mem (inv_mem hh) hT) (by rw [inv_inv]; exact hh)

theorem f4B2Rep_surjective
    : Function.Surjective (f4B2Rep K) := by
  intro A
  have hle : matrixIsometryGroup (f4J0 K) ≤ f4B2Image K := by
    rw [matrixIsometryGroup_f4J0_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    exact f4Trans_mem_image a c
  obtain ⟨B, ⟨g, rfl⟩, hB⟩ := hle A.2
  exact ⟨g, Subtype.ext hB⟩

end CFSG.RankThree.Chevalley.SteinbergBN
