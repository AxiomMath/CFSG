module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150AutL3SL
public import CFSG.GroupTheory.ABGDGroups.LinearStructure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.GH74.GLS.IVK (fixedField fixedField_apply)
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie (uniFix uniFixEquiv comapEquiv
  comap_range_uniFix_facts eq_of_subnormal_of_le_simple isSimpleGroup_comap
  isSimpleGroup_range_uniFix false_of_uniFix_two)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)

section Unitary

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

private theorem fixU {A : unitaryIsom3 h} {δ : F ≃+* F} {g : unitarySU p f F 3}
    (hg : (psuConj h A * psuField h δ) (unitaryProj h 3 g) = unitaryProj h 3 g) :
    ∃ c : F, c ^ 3 = 1 ∧ ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      c • (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map δ *
        (((A : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  have h1 : (psuConj h A * psuField h δ) (unitaryProj h 3 g) =
      unitaryProj h 3 (suConj h A (suField h δ g)) := by
    rw [MulAut.mul_apply]
    change psuConj h A (psuField h δ (g : unitaryPSU h 3)) = _
    rw [psuField_mk, psuConj_mk]
    rfl
  rw [h1] at hg
  obtain ⟨c, -, hc3, hcm⟩ := QuotientGroup.eq.mp hg
  refine ⟨c, ?_, ?_⟩
  · have := congrArg Units.val hc3
    simpa using this
  · have hgl : ((g : unitarySU p f F 3) : GL (Fin 3) F) =
        ((suConj h A (suField h δ g) : unitarySU p f F 3) : GL (Fin 3) F) *
          GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hcm, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have hm := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hgl
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_suConj, coe_suField,
      coe_glAut, Matrix.scalar_apply] at hm
    refine hm.trans ?_
    ext i j
    simp [Matrix.mul_diagonal, mul_comm]

private noncomputable def suMk (M : Matrix (Fin 3) (Fin 3) F) (hdet : M.det = 1)
    (hu : (M.map h.bar)ᵀ * M = 1) : unitarySU p f F 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨hdet, hu⟩⟩

private theorem coe_suMk (M : Matrix (Fin 3) (Fin 3) F) (hdet : M.det = 1)
    (hu : (M.map h.bar)ᵀ * M = 1) :
    (((suMk h M hdet hu : unitarySU p f F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M :=
  rfl

variable {h}

private theorem unitaryProj_mem_range_uniFix {ψ : F ≃+* F} {f₀ : ℕ}
    (h₀ : UnitaryFieldData p f₀ (fixedField ψ))
    (hbar : ∀ x : fixedField ψ, h.bar (x : F) = ((h₀.bar x : fixedField ψ) : F))
    (X : unitarySU p f F 3)
    (hX : ∀ i j, ψ (((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
      ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) :
    unitaryProj h 3 X ∈ (CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.uniFix h h₀ hbar).range := by
  have hX' : suField h ψ X = X := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut]
    ext i j
    exact hX i j
  obtain ⟨g₀, hg₀⟩ := (mem_range_suIncl_iff h h₀ hbar X).mpr hX'
  exact ⟨g₀, by
    rw [CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.uniFix, MonoidHom.comp_apply, hg₀]⟩

section Elements

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private def pm01 : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private def pm12 : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

private theorem det_pm01 (h2 : (2 : F) = 0) : (pm01 : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [pm01, Matrix.det_fin_three]
  linear_combination (-1 : F) * h2

private theorem unitary_pm01 : ((pm01 : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * pm01 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pm01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem det_pm12 (h2 : (2 : F) = 0) : (pm12 : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [pm12, Matrix.det_fin_three]
  linear_combination (-1 : F) * h2

private theorem unitary_pm12 : ((pm12 : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * pm12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pm12, Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def xm (s : F) : Matrix (Fin 3) (Fin 3) F :=
  !![0, h.bar s, 0; s, 0, 0; 0, 0, 1]

private theorem det_xm (h2 : (2 : F) = 0) {s : F} (hs : s * h.bar s = 1) :
    (xm h s : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [xm, Matrix.det_fin_three]
  linear_combination (-1 : F) * hs - h2

private theorem unitary_xm {s : F} (hs : s * h.bar s = 1) :
    ((xm h s : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * xm h s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xm, Matrix.mul_apply, Fin.sum_univ_three,
    UnitaryFieldData.bar_bar, mul_comm, hs]

private def qm (a : F) : Matrix (Fin 3) (Fin 3) F := !![1 + a, a, 0; a, 1 + a, 0; 0, 0, 1]

private theorem det_qm (h2 : (2 : F) = 0) (a : F) : (qm a : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [qm, Matrix.det_fin_three]
  linear_combination a * h2

private theorem unitary_qm (h2 : (2 : F) = 0) {a : F} (ha : h.bar a = a) :
    ((qm a : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * qm a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qm, Matrix.mul_apply, Fin.sum_univ_three, ha]
  all_goals linear_combination (a + a ^ 2) * h2

private theorem trace_pm01 : (pm01 : Matrix (Fin 3) (Fin 3) F).trace = 1 := by
  simp [pm01, Matrix.trace_fin_three]

private theorem trace_pm12 : (pm12 : Matrix (Fin 3) (Fin 3) F).trace = 1 := by
  simp [pm12, Matrix.trace_fin_three]

private theorem trace_xm (s : F) : (xm h s : Matrix (Fin 3) (Fin 3) F).trace = 1 := by
  simp [xm, Matrix.trace_fin_three]

private theorem trace_qm (h2 : (2 : F) = 0) (a : F) :
    (qm a : Matrix (Fin 3) (Fin 3) F).trace = 1 := by
  simp [qm, Matrix.trace_fin_three]
  linear_combination (1 + a) * h2

end Elements

section Rel

variable {f : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 f F}

private theorem rel_of_fixU {A : unitaryIsom3 h} {δ : F ≃+* F} {g : unitarySU 2 f F 3}
    (htr : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace = 1)
    (hg : (psuConj h A * psuField h δ) (unitaryProj h 3 g) = unitaryProj h 3 g) :
    ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map δ =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨c, hc3, hcm⟩ := fixU h hg
  have ht := congrArg Matrix.trace hcm
  rw [Matrix.trace_smul, Matrix.trace_units_conj] at ht
  have hmap : (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map δ).trace =
      δ ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace := by
    simp [Matrix.trace, Matrix.diag, map_sum]
  rw [hmap, htr, map_one] at ht
  have hc1 : c = 1 := by simpa using ht.symm
  rw [hc1, one_smul] at hcm
  calc ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map δ
      = (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map δ *
        (((A : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
          ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    _ = _ := by rw [← hcm]

private theorem scalar_and_fix_of_rels {A : GL (Fin 3) F} {δ : F ≃+* F} {s : F}
    (hs1 : s ≠ 1)
    (R1 : (A : Matrix (Fin 3) (Fin 3) F) * pm01 = pm01 * (A : Matrix (Fin 3) (Fin 3) F))
    (R2 : (A : Matrix (Fin 3) (Fin 3) F) * pm12 = pm12 * (A : Matrix (Fin 3) (Fin 3) F))
    (R3 : (A : Matrix (Fin 3) (Fin 3) F) * (xm h s).map δ =
      xm h s * (A : Matrix (Fin 3) (Fin 3) F)) :
    (A : Matrix (Fin 3) (Fin 3) F) ∈ Set.range (Matrix.scalar (Fin 3)) ∧ δ s = s := by
  set B : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hB
  have a1 : B 0 1 = B 1 0 := by
    have := congrFun (congrFun R1 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, pm01] using this
  have a2 : B 0 0 = B 1 1 := by
    have := congrFun (congrFun R1 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, pm01] using this
  have a3 : B 0 2 = B 1 2 := by
    have := congrFun (congrFun R1 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, pm01] using this
  have a4 : B 2 1 = B 2 0 := by
    have := congrFun (congrFun R1 2) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, pm01] using this
  have b1 : B 0 2 = B 0 1 := by
    have := congrFun (congrFun R2 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, pm12] using this
  have b2 : B 1 0 = B 2 0 := by
    have := congrFun (congrFun R2 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, pm12] using this
  have b3 : B 1 2 = B 2 1 := by
    have := congrFun (congrFun R2 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, pm12] using this
  have b4 : B 1 1 = B 2 2 := by
    have := congrFun (congrFun R2 1) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, pm12] using this
  have c1 : B 0 2 = h.bar s * B 1 2 := by
    have := congrFun (congrFun R3 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, xm] using this
  have c2 : B 1 1 * δ s = s * B 0 0 := by
    have := congrFun (congrFun R3 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, xm] using this
  have hbs1 : h.bar s ≠ 1 := by
    intro h1
    apply hs1
    rw [← h.bar_bar s, h1, map_one]
  have d1 : B 1 2 = 0 := by
    have h1 : B 1 2 * (1 - h.bar s) = 0 := by linear_combination a3.symm.trans c1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (sub_eq_zero.mp h2).symm hbs1
  have d2 : B 0 2 = 0 := by rw [a3, d1]
  have d3 : B 0 1 = 0 := by rw [← b1, d2]
  have d4 : B 1 0 = 0 := by rw [← a1, d3]
  have d5 : B 2 0 = 0 := by rw [← b2, d4]
  have d6 : B 2 1 = 0 := by rw [a4, d5]
  have hscal : B ∈ Set.range (Matrix.scalar (Fin 3)) := by
    refine ⟨B 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, a2, b4, d1, d2, d3, d4, d5, d6]
  refine ⟨hscal, ?_⟩
  have hinv := congrFun (congrFun (Units.mul_inv A) 0) 0
  have hB00 : B 0 0 ≠ 0 := by
    intro h0
    simp [Matrix.mul_apply, Fin.sum_univ_three, ← hB, h0, d3, d2] at hinv
  have c2' : B 0 0 * δ s = s * B 0 0 := by
    calc B 0 0 * δ s = B 1 1 * δ s := by rw [a2]
      _ = s * B 0 0 := c2
  have h1 : B 0 0 * (δ s - s) = 0 := by linear_combination c2'
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 hB00
  · exact sub_eq_zero.mp h2

private theorem map_eq_of_rel_scalar {A : GL (Fin 3) F} {δ : F ≃+* F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) ∈ Set.range (Matrix.scalar (Fin 3)))
    {M : Matrix (Fin 3) (Fin 3) F}
    (R : (A : Matrix (Fin 3) (Fin 3) F) * M.map δ = M * (A : Matrix (Fin 3) (Fin 3) F)) :
    M.map δ = M := by
  obtain ⟨α, hα⟩ := hA
  have hα0 : α ≠ 0 := by
    rintro rfl
    have := congrFun (congrFun (Units.mul_inv A) 0) 0
    simp [← hα] at this
  rw [← hα, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
    ← Matrix.smul_eq_mul_diagonal] at R
  exact smul_right_injective _ hα0 R

private theorem exists_decomp {E : Type} [Field E] (h2 : (2 : E) = 0) (b : E →+* E)
    (hb : ∀ x, b (b x) = x) {s : E} (hs : b s ≠ s) (z : E) :
    ∃ a c : E, b a = a ∧ b c = c ∧ z = a + c * s := by
  have hne : s + b s ≠ 0 := by
    intro h0
    apply hs
    linear_combination h0 - s * h2
  set c := (z + b z) / (s + b s) with hc
  have hbc : b c = c := by
    rw [hc, map_div₀, map_add, map_add, hb, hb, add_comm (b z) z, add_comm (b s) s]
  have hcs : c * (s + b s) = z + b z := by rw [hc]; field_simp
  refine ⟨z + c * s, c, ?_, hbc, ?_⟩
  · rw [map_add, map_mul, hbc]
    linear_combination hcs + (b z - c * s) * h2
  · linear_combination (-(c * s)) * h2

private theorem pm01_map (δ : F ≃+* F) : (pm01 : Matrix (Fin 3) (Fin 3) F).map δ = pm01 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pm01]

private theorem pm12_map (δ : F ≃+* F) : (pm12 : Matrix (Fin 3) (Fin 3) F).map δ = pm12 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pm12]

private theorem psuConj_eq_one_of_scalar {A : unitaryIsom3 h}
    (hA : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ∈ Set.range (Matrix.scalar (Fin 3))) :
    psuConj h A = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_suConj, Units.val_mul, Units.val_mul]
    exact conj_eq_of_mem_range_scalar hA _

theorem unitary_model_eq_one [Finite F] (hq : 2 < 2 ^ f) {ψ : F ≃+* F} {f₀ : ℕ}
    (h₀ : UnitaryFieldData 2 f₀ (fixedField ψ))
    (hbar : ∀ x : fixedField ψ, h.bar (x : F) = ((h₀.bar x : fixedField ψ) : F))
    (hodd : Odd (orderOf ψ)) {t : MulAut (unitaryPSU h 3)} (ht : ∃ m : ℕ, t ^ 2 ^ m = 1)
    (hfix : ∀ x ∈ (uniFix h h₀ hbar).range, t x = x) : t = 1 := by
  obtain ⟨m, hm⟩ := ht
  obtain ⟨A, δ, htA⟩ := exists_psuConj_mul_psuField hq t
  have hchar : CharP F 2 := h.charP
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hE : ∀ X : unitarySU 2 f F 3,
      (∀ i j, ψ (((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
        ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) →
      (psuConj h A * psuField h δ) (unitaryProj h 3 X) = unitaryProj h 3 X := fun X hX => by
    rw [← htA]
    exact hfix _ (unitaryProj_mem_range_uniFix h₀ hbar X hX)
  have R1 : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * pm01 =
      pm01 * ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := rel_of_fixU (A := A) (δ := δ) (g := suMk h pm01 (det_pm01 h2) (unitary_pm01 h))
      (by rw [coe_suMk]; exact trace_pm01)
      (hE _ (fun i j => by rw [coe_suMk]; fin_cases i <;> fin_cases j <;> simp [pm01]))
    rwa [coe_suMk, pm01_map] at this
  have R2 : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * pm12 =
      pm12 * ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := rel_of_fixU (A := A) (δ := δ) (g := suMk h pm12 (det_pm12 h2) (unitary_pm12 h))
      (by rw [coe_suMk]; exact trace_pm12)
      (hE _ (fun i j => by rw [coe_suMk]; fin_cases i <;> fin_cases j <;> simp [pm12]))
    rwa [coe_suMk, pm12_map] at this
  obtain ⟨z, hz⟩ := h₀.exists_bar_ne
  have h2E : (2 : fixedField ψ) = 0 :=
    (fixedField ψ).subtype.injective (by rw [map_ofNat, map_zero]; exact h2)
  have hz0 : z ≠ 0 := fun h0 => hz (by rw [h0, map_zero])
  have hbz0 : h₀.bar z ≠ 0 := fun h0 => hz0 (by rw [← h₀.bar_bar z, h0, map_zero])
  obtain ⟨s₀, hs₀def⟩ : ∃ s₀ : fixedField ψ, s₀ = h₀.bar z / z := ⟨_, rfl⟩
  have hbs₀ : h₀.bar s₀ = z / h₀.bar z := by
    rw [hs₀def, map_div₀, h₀.bar_bar]
  have hs₀n : s₀ * h₀.bar s₀ = 1 := by
    rw [hbs₀, hs₀def]
    field_simp
  have hs₀1 : s₀ ≠ 1 := by
    intro h1
    apply hz
    rw [hs₀def, div_eq_one_iff_eq hz0] at h1
    exact h1
  have hs₀b : h₀.bar s₀ ≠ s₀ := by
    intro hb
    apply hs₀1
    rw [hb] at hs₀n
    have h5 : (s₀ - 1) ^ 2 = 0 := by linear_combination hs₀n + (1 - s₀) * h2E
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h5)
  set s : F := (s₀ : F) with hsdef
  have hs : s * h.bar s = 1 := by
    rw [hsdef, hbar]
    exact congrArg Subtype.val hs₀n
  have hs1 : s ≠ 1 := fun h1 => hs₀1 (Subtype.ext h1)
  have hψs : ψ s = s := fixedField_apply ψ s₀
  have hψbs : ψ (h.bar s) = h.bar s := by
    rw [hsdef, hbar]
    exact fixedField_apply ψ (h₀.bar s₀)
  have R3 : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (xm h s).map δ =
      xm h s * ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := rel_of_fixU (A := A) (δ := δ) (g := suMk h (xm h s) (det_xm h h2 hs) (unitary_xm h hs))
      (by rw [coe_suMk]; exact trace_xm h s)
      (hE _ (fun i j => by
        rw [coe_suMk]
        fin_cases i <;> fin_cases j <;> simp [xm, hψs, hψbs]))
    rwa [coe_suMk] at this
  obtain ⟨hscal, hδs⟩ := scalar_and_fix_of_rels hs1 R1 R2 R3
  have hδa : ∀ a : fixedField ψ, h₀.bar a = a → δ (a : F) = a := by
    intro a ha
    have hba : h.bar (a : F) = a := by rw [hbar, ha]
    have hψa : ψ (a : F) = a := fixedField_apply ψ a
    have := rel_of_fixU (A := A) (δ := δ)
      (g := suMk h (qm (a : F)) (det_qm h2 (a : F)) (unitary_qm h h2 hba))
      (by rw [coe_suMk]; exact trace_qm h2 _)
      (hE _ (fun i j => by
        rw [coe_suMk]
        fin_cases i <;> fin_cases j <;> simp [qm, hψa]))
    rw [coe_suMk] at this
    have h3 := map_eq_of_rel_scalar hscal this
    have h4 := congrFun (congrFun h3 0) 1
    simpa [qm] using h4
  have hδ : ∀ x ∈ fixedField ψ, δ x = x := by
    intro x hx
    obtain ⟨a, c, ha, hc, hxac⟩ := exists_decomp h2E h₀.bar h₀.bar_bar hs₀b (⟨x, hx⟩ : fixedField ψ)
    have hx' : x = (a : F) + (c : F) * s := by
      have := congrArg Subtype.val hxac
      simpa using this
    rw [hx', map_add, map_mul, hδa a ha, hδa c hc, hδs]
  have htfield : t = psuField h δ := by
    rw [htA, psuConj_eq_one_of_scalar hscal, one_mul]
  have hδm : δ ^ 2 ^ m = 1 := by
    have h1 : psuField h (δ ^ 2 ^ m) = 1 := by rw [map_pow, ← htfield]; exact hm
    have := eq_one_of_psuConj_mul_psuField_eq_one (1 : unitaryIsom3 h) (δ ^ 2 ^ m)
      (by rw [map_one, one_mul]; exact h1)
    exact this.1
  rw [htfield, eq_one_of_fix_fixedField hodd hδ hδm, map_one]

end Rel

section Data

variable {f : ℕ} {F : Type} [Field F]

private theorem pow_pow_eq_self {K : Type} [Monoid K] (y : K) (n : ℕ) (hy : y ^ n = y) (j : ℕ) :
    y ^ n ^ j = y := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_mul, ih, hy]

theorem exists_unitaryData_fixedField (h : UnitaryFieldData 2 f F) (ψ : F ≃+* F)
    (hodd : Odd (orderOf ψ)) :
    ∃ (f₀ : ℕ) (h₀ : UnitaryFieldData 2 f₀ (fixedField ψ)), f = orderOf ψ * f₀ ∧
      ∀ x : fixedField ψ, h.bar (x : F) = ((h₀.bar x : fixedField ψ) : F) := by
  have : Finite F := h.finite
  have hcard := CFSG.GH74.GLS.IVK.fixedField_card_pow ψ
  rw [h.card] at hcard
  have hord0 : 0 < orderOf ψ := orderOf_pos ψ
  have hdvd : Nat.card (fixedField ψ) ∣ 2 ^ (2 * f) := by
    rw [← hcard]
    exact dvd_pow_self _ hord0.ne'
  obtain ⟨k, hk, hkE⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hkord : k * orderOf ψ = 2 * f := by
    rw [hkE, ← pow_mul] at hcard
    exact Nat.pow_right_injective le_rfl hcard
  have hordf : orderOf ψ ∣ f := by
    have : orderOf ψ ∣ 2 * f := ⟨k, by rw [← hkord]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd) this)
  obtain ⟨f₀, hf₀⟩ := hordf
  have hk2 : k = 2 * f₀ := by
    have : k * orderOf ψ = (2 * f₀) * orderOf ψ := by rw [hkord, hf₀]; ring
    exact Nat.eq_of_mul_eq_mul_right hord0 this
  have hf₀1 : 1 ≤ f₀ := by
    have := h.one_le
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf₀
      omega
    · exact h0
  have h₀ : UnitaryFieldData 2 f₀ (fixedField ψ) :=
    ⟨Nat.prime_two, hf₀1, by rw [hkE, hk2]⟩
  refine ⟨f₀, h₀, hf₀, fun x => ?_⟩
  have : Fintype (fixedField ψ) := Fintype.ofFinite _
  obtain ⟨j, hj⟩ := hodd
  have hxq : ((x : fixedField ψ) : F) ^ (2 ^ (2 * f₀)) = x := by
    have h1 := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hkE, hk2] at h1
    exact congrArg Subtype.val h1
  have hy : (((x : fixedField ψ) : F) ^ 2 ^ f₀) ^ 2 ^ (2 * f₀) =
      ((x : fixedField ψ) : F) ^ 2 ^ f₀ := by
    rw [← pow_mul, mul_comm, pow_mul, hxq]
  have e1 : (2 : ℕ) ^ f = 2 ^ f₀ * (2 ^ (2 * f₀)) ^ j := by
    rw [hf₀, hj, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, e1, pow_mul,
    pow_pow_eq_self _ _ hy j]
  simp

theorem psuField_injective (h : UnitaryFieldData p f F) : Function.Injective (psuField h) := by
  rw [injective_iff_map_eq_one]
  intro ε hε
  exact (eq_one_of_psuConj_mul_psuField_eq_one (1 : unitaryIsom3 h) ε
    (by rw [map_one, one_mul]; exact hε)).1

end Data

section Bridge

variable {f : ℕ} {F : Type} [Field F]

theorem noTwoCentAut_of_eq_comap_unitary {S : Type} [Group S] {K : Subgroup S}
    [Finite F] (h : UnitaryFieldData 2 f F) (hq : 2 < 2 ^ f) (τ : S ≃* unitaryPSU h 3)
    {ψ : F ≃+* F} {f₀ : ℕ} (h₀ : UnitaryFieldData 2 f₀ (fixedField ψ))
    (hbar : ∀ x : fixedField ψ, h.bar (x : F) = ((h₀.bar x : fixedField ψ) : F))
    (hψodd : Odd (orderOf ψ)) (hKeq : K = (uniFix h h₀ hbar).range.comap τ.toMonoidHom) :
    NoTwoCentAut K := by
  intro t ⟨m, hm⟩ hfix
  have h1 : ∀ x ∈ (uniFix h h₀ hbar).range, MulAut.congr τ t x = x := by
    intro x hx
    have hmem : τ.symm x ∈ K := by
      rw [hKeq]
      simpa using hx
    show τ (t (τ.symm x)) = x
    rw [hfix _ hmem]
    simp
  have h2 : (MulAut.congr τ t) ^ 2 ^ m = 1 := by rw [← map_pow, hm, map_one]
  have h3 := unitary_model_eq_one hq h₀ hbar hψodd ⟨m, h2⟩ h1
  exact (MulAut.congr τ).injective (by rw [h3, map_one])

theorem exists_iso_psuField {S : Type} [Group S] {σ : MulAut S} (h : UnitaryFieldData p f F)
    (e : S ≃* unitaryPSU h 3) (hk : (stdPinnedPSU3 h).HasKind (MulAut.congr e σ) .field) :
    ∃ (τ : S ≃* unitaryPSU h 3) (ψ : F ≃+* F), ψ ≠ 1 ∧ MulAut.congr τ σ = psuField h ψ := by
  obtain ⟨φ, hφ, hφ1, d, hd, hσ⟩ := hk
  obtain ⟨ψ, rfl⟩ := hφ
  obtain ⟨A, rfl⟩ := hd
  refine ⟨e.trans (psuConj h A)⁻¹, ψ, fun h1 => hφ1 (by rw [h1, map_one]), ?_⟩
  have : MulAut.congr (e.trans (psuConj h A)⁻¹) σ =
      (psuConj h A)⁻¹ * MulAut.congr e σ * ((psuConj h A)⁻¹)⁻¹ := by
    ext y
    rfl
  rw [this, hσ]
  group

theorem two_lt_of_perfect_fix {S : Type} [Group S] {σ : MulAut S} {K : Subgroup S}
    (hK : K ≤ Sec4.autFix σ) [Group.IsPerfect K] (hnt : K ≠ ⊥) (h : UnitaryFieldData 2 f F)
    (τ : S ≃* unitaryPSU h 3) {ψ : F ≃+* F} (hστ : MulAut.congr τ σ = psuField h ψ) {f₀ : ℕ}
    (h₀ : UnitaryFieldData 2 f₀ (fixedField ψ))
    (hbar : ∀ x : fixedField ψ, h.bar (x : F) = ((h₀.bar x : fixedField ψ) : F)) :
    2 < 2 ^ f₀ := by
  by_contra hle
  have h1 : 1 ≤ f₀ := h₀.one_le
  have h2 : 2 ^ f₀ = 2 := by
    have : 2 ^ 1 ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) h1
    omega
  exact false_of_uniFix_two h₀ hbar τ hστ h2 (fun x => Iff.rfl) hK hnt

theorem noTwoCentAut_of_field_unitary {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {K : Subgroup S} (hK : K ≤ Sec4.autFix σ) [Group.IsPerfect K] (hnt : K ≠ ⊥)
    (hsub : (K.subgroupOf (Sec4.autFix σ)).IsSubnormal) (hodd : Odd (orderOf σ))
    (h : UnitaryFieldData 2 f F) (hq : 2 < 2 ^ f) (e : S ≃* unitaryPSU h 3)
    (hk : (stdPinnedPSU3 h).HasKind (MulAut.congr e σ) .field) : NoTwoCentAut K := by
  have : Finite F := h.finite
  obtain ⟨τ, ψ, -, hστ⟩ := exists_iso_psuField h e hk
  have hψodd : Odd (orderOf ψ) := by
    rw [← orderOf_injective (psuField h) (psuField_injective h) ψ, ← hστ,
      MulEquiv.orderOf_eq (MulAut.congr τ) σ]
    exact hodd
  obtain ⟨f₀, h₀, -, hbar⟩ := exists_unitaryData_fixedField h ψ hψodd
  have hq₀ := two_lt_of_perfect_fix hK hnt h τ hστ h₀ hbar
  obtain ⟨hJP, hPC⟩ := comap_range_uniFix_facts (h₀ := h₀) (hbar := hbar) τ hστ
    (fun x => Iff.rfl) hK
  have hKeq := eq_of_subnormal_of_le_simple hJP hPC hsub
    (isSimpleGroup_comap τ (isSimpleGroup_range_uniFix h h₀ hbar hq₀)) hnt
  exact noTwoCentAut_of_eq_comap_unitary h hq τ h₀ hbar hψodd hKeq

end Bridge

end Unitary

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150
