module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocE

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.EvenBN.U4 (mem_commutator_range_of_SL2)
open CFSG.LieType.Universal.Spin (upperSL2 coe_upperSL2)
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} [CharP K 2]

theorem lY_le_Ct : lY h ≤ Ct h := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  exact hypProj_mem_Ct (levHom_comm_z₂SU A)

theorem mat_levHom_ee (A : SpecialLinearGroup (Fin 2) h.fixedField) (i j : Fin 2) :
    mat (levHom h A) (.inl i) (.inl j) = slM A i j := by
  rw [levHom_eq_lev, mat_lev]
  simp [oddDiag]

theorem levHom_upper_one_ne : hypProj h 2 1 (levHom h (upperSL2 (1 : h.fixedField))) ≠ 1 := by
  intro e
  have hmem : levHom h (upperSL2 (1 : h.fixedField)) ∈ hypScalars h 2 1 := by
    rw [← ker_hypProj]
    exact e
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_hypScalars hmem
  have := hc (.inl 0) (.inl 1)
  rw [mat_levHom_ee, slM_upperSL2] at this
  simp at this

theorem not_isSolvable_lY (hf : 2 ≤ f) : ¬ Group.IsSolvable ↥(lY h) := by
  intro hsol
  obtain ⟨y, hy0, hy1⟩ := exists_ne_zero_one_F (h := h) hf
  have hl : ((Units.mk0 y hy0 : h.fixedFieldˣ) : h.fixedField) ^ 2 ≠ 1 := by
    intro e
    have h2 : (2 : h.fixedField) = 0 := CharTwo.two_eq_zero
    have e' : (y - 1) * (y - 1) = 0 := by
      simp only [Units.val_mk0] at e
      linear_combination e + (1 - y) * h2
    exact hy1 (sub_eq_zero.1 (mul_self_eq_zero.1 e'))
  have hperf : ⁅lY h, lY h⁆ = lY h := by
    refine le_antisymm (commutator_le_self _) ?_
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    have := mem_commutator_range_of_SL2 ((hypProj h 2 1).comp (levHom h)) hl A
    rwa [MonoidHom.range_comp] at this
  have hcomm : _root_.commutator ↥(lY h) = ⊤ := by
    apply Subgroup.map_injective (lY h).subtype_injective
    have : (_root_.commutator ↥(lY h)).map (lY h).subtype = ⁅lY h, lY h⁆ := by
      unfold _root_.commutator
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [this, hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hn : Nontrivial ↥(lY h) :=
    ⟨⟨⟨_, ⟨_, ⟨upperSL2 1, rfl⟩, rfl⟩⟩, 1, fun e => levHom_upper_one_ne (congrArg Subtype.val e)⟩⟩
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(lY h)
  rw [hcomm] at hlt
  exact lt_irrefl _ hlt

theorem eq_one_of_comm_mem_Uct (A : SpecialLinearGroup (Fin 2) h.fixedField)
    (h1 : ⁅levHom h A, vE11 1⁆ ∈ Uct h) (h2 : ⁅levHom h A, vE22 1⁆ ∈ Uct h) : A = 1 := by
  have c1 := commutator_levHom_Vsub A (Vt_le_Vsub h (vE11_mem_Vt (1 : h.fixedField)))
  have c2 := commutator_levHom_Vsub A (Vt_le_Vsub h (vE22_mem_Vt (1 : h.fixedField)))
  have e1 := (mem_vsub_iff.1 h1)
  obtain ⟨Y1, hY1, ⟨a1, b1, -⟩, hg1⟩ := e1
  obtain ⟨Y2, hY2, ⟨a2, b2, -⟩, hg2⟩ := mem_vsub_iff.1 h2
  have y1 := c1.2
  have y2 := c2.2
  rw [hg1, Yof_vSU hY1, Yof_vE11] at y1
  rw [hg2, Yof_vSU hY2, Yof_vE22] at y2
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have sq0 : ∀ x : K, x * x = 0 → x = 0 := fun x hx => mul_self_eq_zero.1 hx
  have sq1 : ∀ x : K, x * x = 1 → x = 1 := fun x hx => by
    have : (x - 1) * (x - 1) = 0 := by linear_combination hx + (1 - x) * h2K
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  have e00 := congrFun (congrFun y1 0) 0
  have e11 := congrFun (congrFun y1 1) 1
  have f00 := congrFun (congrFun y2 0) 0
  have f11 := congrFun (congrFun y2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11 f00 f11
  have p0 : slM A 0 0 = 1 := sq1 _ (by linear_combination (-1) * e00 + a1 - h2K)
  have r0 : slM A 1 0 = 0 := sq0 _ (by linear_combination (-1) * e11 + b1)
  have q0 : slM A 0 1 = 0 := sq0 _ (by linear_combination (-1) * f00 + a2)
  have s0 : slM A 1 1 = 1 := sq1 _ (by linear_combination (-1) * f11 + b2 - h2K)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [slM_apply] using p0
  · simpa [slM_apply] using q0
  · simpa [slM_apply] using r0
  · simpa [slM_apply] using s0

theorem mem_Uct_of_mem_ucY {g : hypSU h 2 1} (hg : g ∈ Vsub h)
    (hu : hypProj h 2 1 g ∈ ucY h) : g ∈ Uct h := by
  obtain ⟨u, hu, e⟩ := hu
  have hU : ∀ x ∈ Vsub h, x ∈ hypUnitriangular h 2 1 := fun x hx =>
    Ssub_le_Usub (Vsub_le_Ssub hx)
  rwa [← hypProj_eq_of_mem_U (hU u (Uct_le_Vsub h hu)) (hU g hg) e]

theorem nonsolv_Y (hf : 2 ≤ f) : ∃ L : Subgroup (hypPSU h 2 1), L ≤ Ct h ∧
    ¬ Group.IsSolvable ↥L ∧ ∀ L' : Subgroup (hypPSU h 2 1), L' ≤ L →
      (∀ x ∈ L', ∀ v ∈ vY h, x * v * x⁻¹ * v⁻¹ ∈ ucY h) → Group.IsSolvable ↥L' := by
  refine ⟨lY h, lY_le_Ct, not_isSolvable_lY hf, fun L' hL' hcomm => ?_⟩
  have hbot : L' = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall L').2 fun x hx => ?_
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hL' hx
    have key : ∀ w : hypSU h 2 1, w ∈ Vt h → ⁅levHom h A, w⁆ ∈ Uct h := fun w hw => by
      refine mem_Uct_of_mem_ucY (commutator_levHom_Vsub A (Vt_le_Vsub h hw)).1 ?_
      have := hcomm _ hx (hypProj h 2 1 w) ⟨w, hw, rfl⟩
      rw [map_commutatorElement, commutatorElement_def]
      exact this
    rw [eq_one_of_comm_mem_Uct A (key _ (vE11_mem_Vt 1)) (key _ (vE22_mem_Vt 1)), map_one,
      map_one]
  rw [hbot]
  infer_instance

end CFSG.Quasithin.H13.F431.Un.L5
