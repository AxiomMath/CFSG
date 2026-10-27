module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def hypGramTwo (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem gramForm_hypGramTwo (x y : Fin 2 → K) :
    gramForm h (hypGramTwo K) x y = h.bar (x 0) * y 1 + h.bar (x 1) * y 0 := by
  simp [gramForm_apply, hypGramTwo, dotProduct, mulVec, Fin.sum_univ_two]

theorem hypGramTwo_isometry_entries (A : Matrix (Fin 2) (Fin 2) K) :
    (A.map h.bar)ᵀ * hypGramTwo K * A =
      !![h.bar (A 0 0) * A 1 0 + h.bar (A 1 0) * A 0 0,
          h.bar (A 0 0) * A 1 1 + h.bar (A 1 0) * A 0 1;
        h.bar (A 0 1) * A 1 0 + h.bar (A 1 1) * A 0 0,
          h.bar (A 0 1) * A 1 1 + h.bar (A 1 1) * A 0 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypGramTwo, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem hyperbolic_two_mem_iff (A : Matrix (Fin 2) (Fin 2) K) :
    (A.det = 1 ∧ ∀ x y, gramForm h (hypGramTwo K) (A *ᵥ x) (A *ᵥ y) =
      gramForm h (hypGramTwo K) x y) ↔
      A 0 0 ∈ h.fixedField ∧ A 1 1 ∈ h.fixedField ∧ A 0 1 ∈ h.traceZero ∧
        A 1 0 ∈ h.traceZero ∧ A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  rw [gramForm_isometry_iff, hypGramTwo_isometry_entries, det_fin_two,
    UnitaryFieldData.mem_fixedField, UnitaryFieldData.mem_fixedField,
    UnitaryFieldData.mem_traceZero, UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace,
    UnitaryFieldData.trace]
  constructor
  · rintro ⟨hdet, hiso⟩
    have e1 := congrFun (congrFun hiso 0) 0
    have e2 := congrFun (congrFun hiso 1) 1
    have e3 := congrFun (congrFun hiso 0) 1
    simp [hypGramTwo] at e1 e2 e3
    obtain ⟨ha, hd, hc, hb⟩ := hyperbolic_entries h e1 e2 e3 hdet
    exact ⟨ha, hd, hb, hc, hdet⟩
  · rintro ⟨ha, hd, hb, hc, hdet⟩
    have hb' : h.bar (A 0 1) = -A 0 1 := by linear_combination hb
    have hc' : h.bar (A 1 0) = -A 1 0 := by linear_combination hc
    refine ⟨hdet, ?_⟩
    rw [ha, hd, hb', hc']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hypGramTwo] <;>
      first | ring1 | linear_combination hdet

section Iso

variable {h} {τ : K} (hτ : τ ∈ h.traceZero) (hτ0 : τ ≠ 0)

theorem bar_eq_neg_of_mem_traceZero {c : K} (hc : c ∈ h.traceZero) : h.bar c = -c := by
  have : c + h.bar c = 0 := hc
  linear_combination this

theorem mem_traceZero_of_bar_eq_neg {c : K} (hc : h.bar c = -c) : c ∈ h.traceZero := by
  change c + h.bar c = 0
  rw [hc, add_neg_cancel]

include hτ in
theorem mul_mem_fixedField_of_mem_traceZero {b : K} (hb : b ∈ h.traceZero) :
    τ * b ∈ h.fixedField := by
  rw [UnitaryFieldData.mem_fixedField, map_mul, bar_eq_neg_of_mem_traceZero hτ,
    bar_eq_neg_of_mem_traceZero hb, neg_mul_neg]

include hτ in
theorem inv_mul_mem_fixedField_of_mem_traceZero {c : K} (hc : c ∈ h.traceZero) :
    τ⁻¹ * c ∈ h.fixedField := by
  rw [UnitaryFieldData.mem_fixedField, map_mul, map_inv₀, bar_eq_neg_of_mem_traceZero hτ,
    bar_eq_neg_of_mem_traceZero hc, inv_neg, neg_mul_neg]

include hτ in
theorem mul_mem_traceZero_of_mem_fixedField {b : K} (hb : b ∈ h.fixedField) :
    τ * b ∈ h.traceZero := by
  refine mem_traceZero_of_bar_eq_neg ?_
  rw [map_mul, bar_eq_neg_of_mem_traceZero hτ, (UnitaryFieldData.mem_fixedField h).1 hb,
    neg_mul]

include hτ in
theorem inv_mul_mem_traceZero_of_mem_fixedField {b : K} (hb : b ∈ h.fixedField) :
    τ⁻¹ * b ∈ h.traceZero := by
  refine mem_traceZero_of_bar_eq_neg ?_
  rw [map_mul, map_inv₀, bar_eq_neg_of_mem_traceZero hτ, (UnitaryFieldData.mem_fixedField h).1 hb,
    inv_neg, neg_mul]

theorem entries_of_mem (g : gramSU h (hypGramTwo K)) :
    ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 ∈ h.fixedField ∧
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ h.fixedField ∧
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 ∈ h.traceZero ∧
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 ∈ h.traceZero ∧
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
          ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 -
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
          ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
  obtain ⟨hiso, hdet⟩ := (mem_gramSU_iff_isometry).1 g.2
  exact (hyperbolic_two_mem_iff h _).1 ⟨hdet, hiso⟩

@[expose] noncomputable def toFixedMat (g : gramSU h (hypGramTwo K)) :
    Matrix (Fin 2) (Fin 2) h.fixedField :=
  !![⟨_, (entries_of_mem g).1⟩,
      ⟨_, mul_mem_fixedField_of_mem_traceZero hτ (entries_of_mem g).2.2.1⟩;
    ⟨_, inv_mul_mem_fixedField_of_mem_traceZero hτ (entries_of_mem g).2.2.2.1⟩,
      ⟨_, (entries_of_mem g).2.1⟩]

include hτ0 in
theorem map_toFixedMat (g : gramSU h (hypGramTwo K)) :
    (toFixedMat hτ g).map (Subtype.val : h.fixedField → K) =
      diagonal ![τ, 1] * ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        diagonal ![τ⁻¹, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toFixedMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

include hτ0 in
theorem det_toFixedMat (g : gramSU h (hypGramTwo K)) : (toFixedMat hτ g).det = 1 := by
  apply Subtype.ext
  have hdet := (entries_of_mem g).2.2.2.2
  rw [det_fin_two]
  simp only [toFixedMat, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, Subfield.coe_sub, Subfield.coe_mul, Subfield.coe_one]
  field_simp
  linear_combination hdet

@[expose] noncomputable def ofFixedMat (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    Matrix (Fin 2) (Fin 2) K :=
  !![((A : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K),
      τ⁻¹ * ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K);
    τ * ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K),
      ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K)]

include hτ0 in
omit hτ in
theorem ofFixedMat_eq (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    ofFixedMat (τ := τ) A = diagonal ![τ⁻¹, 1] *
      (A : Matrix (Fin 2) (Fin 2) h.fixedField).map (Subtype.val : h.fixedField → K) *
        diagonal ![τ, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofFixedMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

include hτ0 in
omit hτ in
theorem det_ofFixedMat (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    (ofFixedMat (τ := τ) A).det = 1 := by
  have hA := congrArg (Subtype.val : h.fixedField → K) A.2
  rw [det_fin_two] at hA
  simp only [Subfield.coe_sub, Subfield.coe_mul, Subfield.coe_one] at hA
  rw [det_fin_two]
  simp only [ofFixedMat, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp
  linear_combination hA

include hτ hτ0 in
theorem ofFixedMat_mem (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (ofFixedMat (τ := τ) A)
      (by rw [det_ofFixedMat hτ0]; exact one_ne_zero) ∈ gramSU h (hypGramTwo K) := by
  rw [mem_gramSU_iff_isometry, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, and_comm]
  refine (hyperbolic_two_mem_iff h _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0).2
  · exact ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1).2
  · exact inv_mul_mem_traceZero_of_mem_fixedField hτ
      ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1).2
  · exact mul_mem_traceZero_of_mem_fixedField hτ
      ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0).2
  · have := det_ofFixedMat (τ := τ) hτ0 A
    rwa [det_fin_two] at this

include hτ0 in
theorem toFixedMat_mul (g g' : gramSU h (hypGramTwo K)) :
    toFixedMat hτ (g * g') = toFixedMat hτ g * toFixedMat hτ g' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toFixedMat, Matrix.mul_apply, Fin.sum_univ_two, Subgroup.coe_mul, Units.val_mul] <;>
    field_simp

theorem toFixedMat_one : toFixedMat hτ (1 : gramSU h (hypGramTwo K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toFixedMat]

@[expose] noncomputable def toSL :
    gramSU h (hypGramTwo K) →* SpecialLinearGroup (Fin 2) h.fixedField where
  toFun g := ⟨toFixedMat hτ g, det_toFixedMat hτ hτ0 g⟩
  map_one' := Subtype.ext (toFixedMat_one hτ)
  map_mul' g g' := Subtype.ext (toFixedMat_mul hτ hτ0 g g')

theorem coe_toSL (g : gramSU h (hypGramTwo K)) :
    ((toSL hτ hτ0 g : SpecialLinearGroup (Fin 2) h.fixedField) :
      Matrix (Fin 2) (Fin 2) h.fixedField) = toFixedMat hτ g :=
  rfl

@[expose] noncomputable def ofSL (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    gramSU h (hypGramTwo K) :=
  ⟨_, ofFixedMat_mem hτ hτ0 A⟩

theorem coe_ofSL (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    ((ofSL hτ hτ0 A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ofFixedMat (τ := τ) A :=
  rfl

theorem toSL_ofSL (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    toSL hτ hτ0 (ofSL hτ hτ0 A) = A := by
  apply Subtype.ext
  rw [coe_toSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toFixedMat, coe_ofSL, ofFixedMat, hτ0]

theorem ofSL_toSL (g : gramSU h (hypGramTwo K)) : ofSL hτ hτ0 (toSL hτ hτ0 g) = g := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ofSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_toSL, toFixedMat, ofFixedMat, hτ0]

@[expose] noncomputable def hypSLEquiv :
    gramSU h (hypGramTwo K) ≃* SpecialLinearGroup (Fin 2) h.fixedField where
  toFun := toSL hτ hτ0
  invFun := ofSL hτ hτ0
  left_inv := ofSL_toSL hτ hτ0
  right_inv := toSL_ofSL hτ hτ0
  map_mul' := (toSL hτ hτ0).map_mul

theorem coe_hypSLEquiv (g : gramSU h (hypGramTwo K)) :
    ((hypSLEquiv hτ hτ0 g : Matrix (Fin 2) (Fin 2) h.fixedField)).map
        (Subtype.val : h.fixedField → K) =
      diagonal ![τ, 1] * ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        diagonal ![τ⁻¹, 1] :=
  map_toFixedMat hτ hτ0 g

theorem coe_hypSLEquiv_symm (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    (((hypSLEquiv hτ hτ0).symm A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![((A : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K),
          τ⁻¹ * ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K);
        τ * ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K),
          ((A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K)] :=
  rfl

end Iso

theorem hyperbolic_two_transvection_generation {V : Type*} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : Module.finrank K V = 2) :
    Subgroup.closure (unitaryTransvections h B) = sesqSpecialUnitaryGroup B :=
  unitary_transvection_generation h hB hBl (by omega) (by rw [hV]; simp)

end CFSG.RankThree.CentralLiftU
