module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.MS93

open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

abbrev SL3 (F : Type) [Field F] : Type := Matrix.SpecialLinearGroup (Fin 3) F

@[expose] def rootElt (i j : Fin 3) (c : F) : SL3 F :=
  if h : i = j then 1 else SpecialLinearGroup.transvection h c

theorem rootElt_of_ne {i j : Fin 3} (h : i ≠ j) (c : F) :
    rootElt i j c = SpecialLinearGroup.transvection h c := by
  simp [rootElt, h]

theorem rootElt_self (i : Fin 3) (c : F) : rootElt i i c = 1 := by
  simp [rootElt]

theorem coe_rootElt {i j : Fin 3} (h : i ≠ j) (c : F) :
    ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 + single i j c := by
  rw [rootElt_of_ne h]
  rfl

@[simp] theorem rootElt_zero (i j : Fin 3) : rootElt i j (0 : F) = 1 := by
  by_cases h : i = j
  · simp [rootElt, h]
  · rw [rootElt_of_ne h, SpecialLinearGroup.transvection_coeff_zero]

theorem rootElt_add (i j : Fin 3) (c d : F) :
    rootElt i j (c + d) = rootElt i j c * rootElt i j d := by
  by_cases h : i = j
  · simp [rootElt, h]
  · simp only [rootElt_of_ne h, SpecialLinearGroup.transvection_add]

theorem rootElt_neg (i j : Fin 3) (c : F) : rootElt i j (-c) = (rootElt i j c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootElt_add, neg_add_cancel, rootElt_zero]

theorem rootElt_injective {i j : Fin 3} (h : i ≠ j) :
    Function.Injective (rootElt i j : F → SL3 F) := by
  intro c d hcd
  have := congrArg (fun g : SL3 F => (g : Matrix (Fin 3) (Fin 3) F) i j) hcd
  simpa [coe_rootElt h, Matrix.one_apply, Matrix.single_apply, h] using this

theorem rootElt_eq_one_iff {i j : Fin 3} (h : i ≠ j) (c : F) : rootElt i j c = 1 ↔ c = 0 := by
  rw [← rootElt_zero i j]
  exact (rootElt_injective h).eq_iff

theorem rootElt_commutator {i j l : Fin 3} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (c d : F) :
    ⁅rootElt i j c, rootElt j l d⁆ = rootElt i l (c * d) := by
  rw [rootElt_of_ne hij, rootElt_of_ne hjl, rootElt_of_ne hil]
  exact SpecialLinearGroup.commutatorElement_transvection hij hjl hil c d

theorem rootElt_commute {i j k l : Fin 3} (hjk : j ≠ k) (hli : l ≠ i) (c d : F) :
    Commute (rootElt i j c) (rootElt k l d) := by
  by_cases hij : i = j
  · rw [hij, rootElt_self]; exact Commute.one_left _
  by_cases hkl : k = l
  · rw [hkl, rootElt_self]; exact Commute.one_right _
  rw [rootElt_of_ne hij, rootElt_of_ne hkl]
  exact SpecialLinearGroup.commute_transvection hij hkl hjk hli c d

@[expose] def rootGroup (i j : Fin 3) : Subgroup (SL3 F) where
  carrier := Set.range (rootElt i j)
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, rootElt_add i j c d⟩
  one_mem' := ⟨0, rootElt_zero i j⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨-c, rootElt_neg i j c⟩

theorem mem_rootGroup {i j : Fin 3} {g : SL3 F} : g ∈ rootGroup i j ↔ ∃ c, rootElt i j c = g :=
  Iff.rfl

theorem rootElt_mem_rootGroup (i j : Fin 3) (c : F) : rootElt i j c ∈ rootGroup i j :=
  ⟨c, rfl⟩

@[expose] def qPt : Subgroup (SL3 F) := rootGroup 0 1 ⊔ rootGroup 0 2

@[expose] def qLn : Subgroup (SL3 F) := rootGroup 0 2 ⊔ rootGroup 1 2

@[expose] def sStar : Subgroup (SL3 F) := rootGroup 0 1 ⊔ rootGroup 0 2 ⊔ rootGroup 1 2

theorem rootGroup_le_qPt : rootGroup 0 2 ≤ (qPt : Subgroup (SL3 F)) := le_sup_right

theorem rootGroup_le_qLn : rootGroup 0 2 ≤ (qLn : Subgroup (SL3 F)) := le_sup_left

theorem qPt_le_sStar : (qPt : Subgroup (SL3 F)) ≤ sStar := le_sup_left

theorem qLn_le_sStar : (qLn : Subgroup (SL3 F)) ≤ sStar := by
  rw [qLn, sStar]
  exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem mem_qLn_iff {g : SL3 F} : g ∈ qLn ↔ ∃ a b : F, rootElt 0 2 a * rootElt 1 2 b = g := by
  have hc : ∀ a b : F, rootElt 1 2 b * rootElt 0 2 a = rootElt 0 2 a * rootElt 1 2 b :=
    fun a b => ((rootElt_commute (by decide) (by decide) a b).eq).symm
  let P : Subgroup (SL3 F) :=
    { carrier := {g | ∃ a b : F, rootElt 0 2 a * rootElt 1 2 b = g}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        refine ⟨a + a', b + b', ?_⟩
        have e : rootElt 0 2 a' * (rootElt 1 2 b * rootElt 1 2 b') =
            rootElt 1 2 b * (rootElt 0 2 a' * rootElt 1 2 b') := by
          rw [← mul_assoc, ← mul_assoc, hc]
        rw [rootElt_add, rootElt_add]
        simp only [mul_assoc, e]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        refine ⟨-a, -b, ?_⟩
        rw [rootElt_neg, rootElt_neg, ← _root_.mul_inv_rev, hc] }
  constructor
  · intro hg
    have hle : qLn ≤ P := by
      rw [qLn]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨a, 0, by simp⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨0, b, by simp⟩
    exact hle hg
  · rintro ⟨a, b, rfl⟩
    exact Subgroup.mul_mem_sup (rootElt_mem_rootGroup _ _ _) (rootElt_mem_rootGroup _ _ _)

@[expose] def cyc : SL3 F :=
  ⟨Matrix.of fun i j => if i = j + 1 then 1 else 0, by
    simp [Matrix.det_fin_three]⟩

theorem coe_cyc : ((cyc : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    Matrix.of fun i j => if i = j + 1 then 1 else 0 :=
  rfl

theorem cyc_mul_rootElt (i j : Fin 3) (c : F) :
    cyc * rootElt i j c = rootElt (i + 1) (j + 1) c * cyc := by
  by_cases h : i = j
  · subst h
    simp [rootElt_self]
  have h' : i + 1 ≠ j + 1 := fun e => h (add_right_cancel e)
  apply Subtype.ext
  change ((cyc : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt i j c : SL3 F) : Matrix _ _ F) =
    ((rootElt (i + 1) (j + 1) c : SL3 F) : Matrix _ _ F) * ((cyc : SL3 F) : Matrix _ _ F)
  rw [coe_rootElt h, coe_rootElt h', coe_cyc]
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] at h ⊢

theorem cyc_conj_rootElt (i j : Fin 3) (c : F) :
    cyc * rootElt i j c * cyc⁻¹ = rootElt (i + 1) (j + 1) c := by
  rw [mul_inv_eq_iff_eq_mul, cyc_mul_rootElt]

@[expose] noncomputable def diagPt (l : F) (hl : l ≠ 0) : SL3 F :=
  SpecialLinearGroup.diag2n (show (0 : Fin 3) ≠ 1 by decide) l hl

theorem diagPt_conj_rootElt (l : F) (hl : l ≠ 0) (c : F) :
    diagPt l hl * rootElt 0 2 c * (diagPt l hl)⁻¹ = rootElt 0 2 (l * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change ((diagPt l hl : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt 0 2 c : SL3 F) :
      Matrix _ _ F) = ((rootElt 0 2 (l * c) : SL3 F) : Matrix _ _ F) *
      ((diagPt l hl : SL3 F) : Matrix _ _ F)
  rw [coe_rootElt (show (0 : Fin 3) ≠ 2 by decide), coe_rootElt (show (0 : Fin 3) ≠ 2 by decide),
    diagPt, SpecialLinearGroup.diag2n_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply]

theorem exists_conj_rootElt_eq {a : F} (ha : a ≠ 0) (c : F) (hc : c ≠ 0) :
    ∃ h : SL3 F, h * rootElt 0 2 a * h⁻¹ = rootElt 0 2 c :=
  ⟨diagPt (c * a⁻¹) (mul_ne_zero hc (inv_ne_zero ha)), by
    rw [diagPt_conj_rootElt, mul_assoc, inv_mul_cancel₀ ha, mul_one]⟩

theorem closure_rootElt_eq_top :
    Subgroup.closure {g : SL3 F | ∃ (i j : Fin 3) (c : F), i ≠ j ∧ rootElt i j c = g} = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  exact Subgroup.subset_closure ⟨i, j, c, hij, rootElt_of_ne hij c⟩

theorem eq_top_of_rootElt_mem {H : Subgroup (SL3 F)}
    (h : ∀ (i j : Fin 3) (c : F), i ≠ j → rootElt i j c ∈ H) : H = ⊤ := by
  rw [eq_top_iff, ← closure_rootElt_eq_top, Subgroup.closure_le]
  rintro _ ⟨i, j, c, hij, rfl⟩
  exact h i j c hij

end CFSG.Quasithin.MS93
