module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHermitian
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverRootData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryLine

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI.TwoCoreGrowth

variable {K : Type} [Field K] (J : HermitianForm 3 K)

@[expose] def diag3 (a b c : Kˣ) : GL (Fin 3) K where
  val := !![(a : K), 0, 0; 0, (b : K), 0; 0, 0, (c : K)]
  inv := !![((a⁻¹ : Kˣ) : K), 0, 0; 0, ((b⁻¹ : Kˣ) : K), 0; 0, 0, ((c⁻¹ : Kˣ) : K)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem coe_diag3 (a b c : Kˣ) :
    (diag3 a b c : Matrix (Fin 3) (Fin 3) K) =
      !![(a : K), 0, 0; 0, (b : K), 0; 0, 0, (c : K)] :=
  rfl

theorem coe_diag3_inv (a b c : Kˣ) :
    (((diag3 a b c)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![((a⁻¹ : Kˣ) : K), 0, 0; 0, ((b⁻¹ : Kˣ) : K), 0; 0, 0, ((c⁻¹ : Kˣ) : K)] :=
  rfl

theorem diag3_mul (a b c a' b' c' : Kˣ) :
    diag3 a b c * diag3 a' b' c' = diag3 (a * a') (b * b') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag3, Matrix.mul_apply, Fin.sum_univ_three]

theorem diag3_one : diag3 (1 : Kˣ) 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag3]

@[expose] def normOne : Subgroup Kˣ where
  carrier := {c | (c : K) * J.conj c = 1}
  mul_mem' {c d} hc hd := by
    change (c : K) * J.conj c = 1 at hc
    change (d : K) * J.conj d = 1 at hd
    change ((c * d : Kˣ) : K) * J.conj ((c * d : Kˣ) : K) = 1
    rw [Units.val_mul, map_mul]
    linear_combination (d : K) * J.conj (d : K) * hc + hd
  one_mem' := by
    change ((1 : Kˣ) : K) * J.conj ((1 : Kˣ) : K) = 1
    simp
  inv_mem' {c} hc := by
    change (c : K) * J.conj c = 1 at hc
    change ((c⁻¹ : Kˣ) : K) * J.conj ((c⁻¹ : Kˣ) : K) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hc, inv_one]

theorem mem_normOne {c : Kˣ} : c ∈ normOne J ↔ (c : K) * J.conj c = 1 :=
  Iff.rfl

theorem conj_eq_inv_of_mem_normOne {c : Kˣ} (hc : c ∈ normOne J) :
    J.conj (c : K) = (c : K)⁻¹ :=
  (eq_inv_of_mul_eq_one_right hc)

@[expose] def scalarCenter : Subgroup J.specialSubgroup where
  carrier := {g | ∃ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c ∧
    c * J.conj c = 1 ∧ c ^ 3 = 1}
  mul_mem' := by
    rintro g g' ⟨c, hc, hcn, hc3⟩ ⟨c', hc', hcn', hc3'⟩
    refine ⟨c * c', ?_, ?_, by rw [mul_pow, hc3, hc3', one_mul]⟩
    · rw [Subgroup.coe_mul, Units.val_mul, hc, hc', scalar_apply, scalar_apply, scalar_apply,
        diagonal_mul_diagonal]
    · rw [map_mul]
      linear_combination c' * J.conj c' * hcn + hcn'
  one_mem' := ⟨1, by simp, by simp, by simp⟩
  inv_mem' := by
    rintro g ⟨c, hc, hcn, hc3⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hcn
    refine ⟨c⁻¹, ?_, by rw [map_inv₀, ← mul_inv, hcn, inv_one],
      by rw [inv_pow, hc3, inv_one]⟩
    have hmul : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((g⁻¹ : J.specialSubgroup) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    rw [hc] at hmul
    calc (((g⁻¹ : J.specialSubgroup) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = scalar (Fin 3) c⁻¹ * (scalar (Fin 3) c *
            (((g⁻¹ : J.specialSubgroup) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          rw [← Matrix.mul_assoc, scalar_apply, scalar_apply, diagonal_mul_diagonal,
            inv_mul_cancel₀ hc0, diagonal_one, Matrix.one_mul]
      _ = scalar (Fin 3) c⁻¹ := by rw [hmul, Matrix.mul_one]

theorem mem_scalarCenter {g : J.specialSubgroup} :
    g ∈ scalarCenter J ↔ ∃ c : K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c ∧
        c * J.conj c = 1 ∧ c ^ 3 = 1 :=
  Iff.rfl

theorem mem_scalarCenter_of_scalar (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {g : J.specialSubgroup} {c : K}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c) :
    g ∈ scalarCenter J := by
  obtain ⟨hgram, hdet⟩ := (J.mem_specialSubgroup_iff (g : GL (Fin 3) K)).mp g.2
  rw [hg] at hgram
  refine ⟨c, hg, ?_, ?_⟩
  · have h := congrArg (fun B => B 0 2) hgram
    simp only [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
      scalar_apply, diagonal_apply] at h
    simpa [mul_comm] using h
  · have h := congrArg Units.val hdet
    rw [GeneralLinearGroup.val_det_apply, Units.val_one, hg, det_fin_three] at h
    simpa [scalar_apply, diagonal_apply, pow_succ] using h

theorem scalarCenter_eq_ker (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    scalarCenter J = (psuMk J).ker := by
  ext g
  rw [MonoidHom.mem_ker, psuMk_eq_one_iff]
  constructor
  · rintro ⟨c, hc, hcn, -⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hcn
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, hc]
  · rintro ⟨u, hu⟩
    refine mem_scalarCenter_of_scalar J hJ (c := u) ?_
    rw [← hu, GeneralLinearGroup.coe_scalar]

theorem scalarCenter_le_center : scalarCenter J ≤ Subgroup.center J.specialSubgroup := by
  rintro g ⟨c, hc, -, -⟩
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc]
  exact ((Matrix.scalar_commute c (fun r => Commute.all c r) _)).eq.symm

variable (C : Subgroup J.specialSubgroup) [C.Normal]

omit [C.Normal] in
theorem le_ker_psuMk (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : C ≤ (psuMk J).ker :=
  hC.trans (scalarCenter_eq_ker J hJ).le

@[expose] def coverToPSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    J.specialSubgroup ⧸ C →* ProjectiveSpecialUnitaryMatrixGroup J :=
  QuotientGroup.lift C (psuMk J) (le_ker_psuMk J C hJ hC)

@[expose] def coverToPGL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : J.specialSubgroup ⧸ C →* ProjGenLinGroup (Fin 3) K :=
  (ProjectiveSpecialUnitaryMatrixGroup J).subtype.comp (coverToPSU J C hJ hC)

variable {J C}

theorem coverToPSU_mk (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    (g : J.specialSubgroup) : coverToPSU J C hJ hC (g : J.specialSubgroup ⧸ C) = psuMk J g :=
  rfl

theorem coverToPGL_mk (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    (g : J.specialSubgroup) :
    coverToPGL J C hJ hC (g : J.specialSubgroup ⧸ C) = ProjGenLinGroup.mk (g : GL (Fin 3) K) :=
  rfl

theorem coverToPSU_surjective (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : Function.Surjective (coverToPSU J C hJ hC) := by
  intro x
  obtain ⟨g, rfl⟩ := psuMk_surjective x
  exact ⟨g, rfl⟩

omit [C.Normal] in
theorem mk_eq_mk_iff {g g' : J.specialSubgroup} :
    (g : J.specialSubgroup ⧸ C) = g' ↔ ∃ c ∈ C, g * c = g' := by
  rw [QuotientGroup.eq]
  exact ⟨fun h => ⟨g⁻¹ * g', h, mul_inv_cancel_left g g'⟩, fun ⟨c, hc, hgc⟩ => by
    rwa [← hgc, inv_mul_cancel_left]⟩

omit [C.Normal] in
theorem exists_scalar_of_mk_eq (hC : C ≤ scalarCenter J) {g g' : J.specialSubgroup}
    (h : (g : J.specialSubgroup ⧸ C) = g') :
    ∃ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) c =
      ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧ c * J.conj c = 1 ∧ c ^ 3 = 1 := by
  obtain ⟨z, hz, hgz⟩ := mk_eq_mk_iff.mp h
  obtain ⟨c, hc, hcn, hc3⟩ := hC hz
  refine ⟨c, ?_, hcn, hc3⟩
  rw [← hgz, Subgroup.coe_mul, Units.val_mul, hc]

@[expose] def sublineMatrix (m : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![m 0 0, 0, m 0 1; 0, 1, 0; m 1 0, 0, m 1 1]

theorem sublineMatrix_mul (m n : Matrix (Fin 2) (Fin 2) K) :
    sublineMatrix (m * n) = sublineMatrix m * sublineMatrix n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sublineMatrix, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem sublineMatrix_one : sublineMatrix (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sublineMatrix]

theorem sublineMatrix_injective :
    Function.Injective (sublineMatrix : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 3) (Fin 3) K) := by
  intro m n h
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 2) 0
  · exact congrFun (congrFun h 2) 2

@[expose] def sublineMonoidHom : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := sublineMatrix
  map_one' := sublineMatrix_one
  map_mul' := sublineMatrix_mul

@[expose] def sl2Embed : SpecialLinearGroup (Fin 2) K →* GL (Fin 3) K :=
  (Units.map sublineMonoidHom).comp SpecialLinearGroup.toGL

theorem coe_sl2Embed (m : SpecialLinearGroup (Fin 2) K) :
    (sl2Embed m : Matrix (Fin 3) (Fin 3) K) = sublineMatrix (m : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem sl2Embed_injective : Function.Injective (sl2Embed : SpecialLinearGroup (Fin 2) K → _) :=
  fun _ _ h => Subtype.ext (sublineMatrix_injective (congrArg Units.val h))

theorem specialLinearGroup_map_injective {F : Type} [Field F] {f : F →+* K}
    (hf : Function.Injective f) :
    Function.Injective (SpecialLinearGroup.map (n := Fin 2) f) := by
  intro _ _ h
  ext i j
  have h' := congrArg (fun x : SpecialLinearGroup (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K) i j) h
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply] at h'
  exact hf h'

variable (J) in
noncomputable abbrev fixedToK : unitaryCoverFixedField J →+* K :=
  (unitaryCoverFixedField J).subtype

theorem conj_fixedToK (x : unitaryCoverFixedField J) : J.conj (fixedToK J x) = fixedToK J x :=
  x.2

section CharTwo

variable [CharP K 2]

theorem sl2Embed_map_mem (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) :
    sl2Embed (SpecialLinearGroup.map (fixedToK J) m) ∈ J.specialSubgroup := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set a := fixedToK J (m 0 0)
  set b := fixedToK J (m 0 1)
  set c := fixedToK J (m 1 0)
  set d := fixedToK J (m 1 1)
  have ha : J.conj a = a := conj_fixedToK _
  have hb : J.conj b = b := conj_fixedToK _
  have hc : J.conj c = c := conj_fixedToK _
  have hd : J.conj d = d := conj_fixedToK _
  have hdet : a * d - b * c = 1 := by
    have := congrArg (fixedToK J) (m.2)
    rw [det_fin_two, map_one, map_sub, map_mul, map_mul] at this
    exact this
  have hM : (sl2Embed (SpecialLinearGroup.map (fixedToK J) m) : Matrix (Fin 3) (Fin 3) K) =
      !![a, 0, b; 0, 1, 0; c, 0, d] := by
    rfl
  rw [HermitianForm.mem_specialSubgroup_iff]
  refine ⟨?_, ?_⟩
  · rw [hM, hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, ha, hb, hc, hd]
    · linear_combination a * c * h2
    · linear_combination hdet + b * c * h2
    · linear_combination hdet + b * c * h2
    · linear_combination b * d * h2
  · rw [Units.ext_iff, GeneralLinearGroup.val_det_apply, hM, Units.val_one]
    simp [det_fin_three]
    linear_combination hdet

variable (J) in
@[expose] def sublineHom (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) →* J.specialSubgroup :=
  (sl2Embed.comp (SpecialLinearGroup.map (fixedToK J))).codRestrict J.specialSubgroup
    (sl2Embed_map_mem hJ)

theorem coe_sublineHom (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) :
    (((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![fixedToK J (m 0 0), 0, fixedToK J (m 0 1); 0, 1, 0;
        fixedToK J (m 1 0), 0, fixedToK J (m 1 1)] :=
  rfl

theorem sublineHom_injective (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (sublineHom J hJ) := by
  intro m n h
  have h' := congrArg (fun g : J.specialSubgroup => (g : GL (Fin 3) K)) h
  have hmap := sl2Embed_injective h'
  exact specialLinearGroup_map_injective (fixedToK J).injective hmap

variable (J C) in
@[expose] def sublineL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (J.specialSubgroup ⧸ C) :=
  ((QuotientGroup.mk' C).comp (sublineHom J hJ)).range

@[expose] def upperSL (F : Type) [Field F] : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun t := SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t.toAdd
  map_one' := SpecialLinearGroup.transvection_coeff_zero _
  map_mul' s t := SpecialLinearGroup.transvection_add _ _ _

@[expose] def lowerSL (F : Type) [Field F] : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun t := SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t.toAdd
  map_one' := SpecialLinearGroup.transvection_coeff_zero _
  map_mul' s t := SpecialLinearGroup.transvection_add _ _ _

theorem coe_upperSL {F : Type} [Field F] (t : Multiplicative F) :
    (upperSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, t.toAdd; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperSL, SpecialLinearGroup.transvection_coe]

theorem coe_lowerSL {F : Type} [Field F] (t : Multiplicative F) :
    (lowerSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t.toAdd, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerSL, SpecialLinearGroup.transvection_coe]

theorem coe_sublineHom_upperSL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (t : Multiplicative (unitaryCoverFixedField J)) :
    (((sublineHom J hJ (upperSL _ t) : J.specialSubgroup) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![1, 0, fixedToK J t.toAdd; 0, 1, 0; 0, 0, 1] := by
  rw [coe_sublineHom, coe_upperSL]
  simp

theorem coe_sublineHom_lowerSL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (t : Multiplicative (unitaryCoverFixedField J)) :
    (((sublineHom J hJ (lowerSL _ t) : J.specialSubgroup) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 0; fixedToK J t.toAdd, 0, 1] := by
  rw [coe_sublineHom, coe_lowerSL]
  simp

variable (J C) in
@[expose] def upperRootL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (J.specialSubgroup ⧸ C) :=
  ((QuotientGroup.mk' C).comp ((sublineHom J hJ).comp (upperSL _))).range

variable (J C) in
@[expose] def lowerRootL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (J.specialSubgroup ⧸ C) :=
  ((QuotientGroup.mk' C).comp ((sublineHom J hJ).comp (lowerSL _))).range

theorem upperRootL_le_sublineL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    upperRootL J C hJ ≤ sublineL J C hJ := by
  rintro _ ⟨t, rfl⟩
  exact ⟨upperSL _ t, rfl⟩

theorem lowerRootL_le_sublineL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    lowerRootL J C hJ ≤ sublineL J C hJ := by
  rintro _ ⟨t, rfl⟩
  exact ⟨lowerSL _ t, rfl⟩

end CharTwo

theorem diag3_torus_mem (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {c : Kˣ}
    (hc : c ∈ normOne J) : diag3 c (c⁻¹ ^ 2) c ∈ J.specialSubgroup := by
  have hc' : J.conj (c : K) = (c : K)⁻¹ := conj_eq_inv_of_mem_normOne J hc
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  rw [HermitianForm.mem_specialSubgroup_iff]
  refine ⟨?_, ?_⟩
  · rw [coe_diag3, hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hc', hc0]
  · rw [Units.ext_iff, GeneralLinearGroup.val_det_apply, coe_diag3, Units.val_one, det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons]
    simp
    field_simp

variable (J) in
@[expose] def torusHom (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    normOne J →* J.specialSubgroup where
  toFun c := ⟨diag3 (c : Kˣ) ((c : Kˣ)⁻¹ ^ 2) (c : Kˣ), diag3_torus_mem hJ c.2⟩
  map_one' := by
    apply Subtype.ext
    simp only [OneMemClass.coe_one, inv_one, one_pow]
    exact diag3_one
  map_mul' c d := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, diag3_mul]
    congr 1
    rw [mul_inv, mul_pow]

theorem coe_torusHom (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (c : normOne J) :
    ((torusHom J hJ c : J.specialSubgroup) : GL (Fin 3) K) =
      diag3 (c : Kˣ) ((c : Kˣ)⁻¹ ^ 2) c :=
  rfl

variable (J C) in
@[expose] def torusL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (J.specialSubgroup ⧸ C) :=
  ((QuotientGroup.mk' C).comp (torusHom J hJ)).range

theorem diag3_one_mem_unitary (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {d : Kˣ}
    (hd : d ∈ normOne J) : diag3 1 d 1 ∈ J.unitarySubgroup := by
  have hd' : J.conj (d : K) * d = 1 := by rw [mul_comm]; exact hd
  rw [HermitianForm.mem_unitarySubgroup_iff, coe_diag3, hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hd']

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
