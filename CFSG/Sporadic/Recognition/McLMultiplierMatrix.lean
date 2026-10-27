module

public import CFSG.Sporadic.Recognition.McLMultiplierInputs
public import CFSG.Sporadic.McL.VecSpec

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.F3.Native CFSG.LieType.Multipliers CFSG.Sporadic.VecOrbit

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Eval

variable (E Ei : ℕ → Array V)

theorem mclEvalM_facts (hE : ∀ i : Fin 6, (E i).size = 42 ∧ RowsWF (E i))
    (hEi : ∀ i : Fin 6, (Ei i).size = 42 ∧ RowsWF (Ei i)) (w : List (Fin 6 × Bool)) :
    (mclEvalM E Ei w).size = 42 ∧ RowsWF (mclEvalM E Ei w) := by
  induction w with
  | nil => exact ⟨idM_size 42, RowsWF.idM 42⟩
  | cons l w ih =>
    have hl : (if l.2 then E l.1.val else Ei l.1.val).size = 42 ∧
        RowsWF (if l.2 then E l.1.val else Ei l.1.val) := by
      split_ifs
      · exact hE l.1
      · exact hEi l.1
    exact ⟨(mul_size 42 _ _).trans hl.1, RowsWF.mul _ 42 hl.2 ih.2⟩

theorem toMat_mclEvalM (g : Fin 6 → GL (Fin 42) (ZMod 3))
    (hE : ∀ i : Fin 6, (E i).size = 42 ∧ RowsWF (E i))
    (hEi : ∀ i : Fin 6, (Ei i).size = 42 ∧ RowsWF (Ei i))
    (hg : ∀ i : Fin 6, toMat 42 (E i.val) = ((g i : GL (Fin 42) (ZMod 3)) :
      Matrix (Fin 42) (Fin 42) (ZMod 3)))
    (hgi : ∀ i : Fin 6, toMat 42 (Ei i.val) = (((g i)⁻¹ : GL (Fin 42) (ZMod 3)) :
      Matrix (Fin 42) (Fin 42) (ZMod 3)))
    (w : List (Fin 6 × Bool)) :
    toMat 42 (mclEvalM E Ei w) = ((FreeGroup.lift g (FreeGroup.mk w) : GL (Fin 42) (ZMod 3)) :
      Matrix (Fin 42) (Fin 42) (ZMod 3)) := by
  induction w with
  | nil =>
    have : FreeGroup.mk ([] : List (Fin 6 × Bool)) = 1 := rfl
    rw [this, map_one, Units.val_one]
    exact toMat_idM 42
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have hl : (if b then E i.val else Ei i.val).size = 42 ∧
        RowsWF (if b then E i.val else Ei i.val) := by
      split_ifs
      · exact hE i
      · exact hEi i
    have hw := mclEvalM_facts E Ei hE hEi w
    have hlet : toMat 42 (if b then E i.val else Ei i.val) =
        ((FreeGroup.lift g (FreeGroup.mk [(i, b)]) : GL (Fin 42) (ZMod 3)) :
          Matrix (Fin 42) (Fin 42) (ZMod 3)) := by
      cases b
      · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of]
        exact hgi i
      · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
        exact hg i
    have e : FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w := rfl
    have hmul : toMat 42 (mclEvalM E Ei ((i, b) :: w)) =
        toMat 42 (if b then E i.val else Ei i.val) * toMat 42 (mclEvalM E Ei w) :=
      toMat_mul hl.1 hl.2 hw.2
    rw [hmul, ih, hlet, e, map_mul, Units.val_mul]

end Eval

theorem coverRelators_mclCommW : coverRelators (wordSet mclRels) mclCommW = wordSet mclCover :=
  coverRelators_wordSet mclRels mclCommWord

theorem exists_hom_of_matCheckOf (E Ei : ℕ → Array V) (h : mclMatCheckOf E Ei = true) :
    ∃ φ : MclCover →* GL (Fin 42) (ZMod 3),
      φ (PresentedGroup.mk _ (FreeGroup.mk mclR0)) ≠ 1 ∧
        φ (PresentedGroup.mk _ (FreeGroup.mk mclR0)) ^ 3 = 1 := by
  unfold mclMatCheckOf at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hmats, hcov⟩, hZc⟩, hZne⟩, hZ3⟩ := h
  have hE : ∀ i : Fin 6, (E i.val).size = 42 ∧ RowsWF (E i.val) := fun i => by
    have := (hmats i.val i.isLt).1.1.1
    exact ⟨(canonM_spec this).1, RowsWF.of_canonM this⟩
  have hEi : ∀ i : Fin 6, (Ei i.val).size = 42 ∧ RowsWF (Ei i.val) := fun i => by
    have := (hmats i.val i.isLt).1.1.2
    exact ⟨(canonM_spec this).1, RowsWF.of_canonM this⟩
  have hinv1 : ∀ i : Fin 6, toMat 42 (E i.val) * toMat 42 (Ei i.val) = 1 := fun i => by
    rw [← toMat_mul (hE i).1 (hE i).2 (hEi i).2, toMat_eq_of_eqM (hmats i.val i.isLt).1.2,
      toMat_idM]
  have hinv2 : ∀ i : Fin 6, toMat 42 (Ei i.val) * toMat 42 (E i.val) = 1 := fun i => by
    rw [← toMat_mul (hEi i).1 (hEi i).2 (hE i).2, toMat_eq_of_eqM (hmats i.val i.isLt).2,
      toMat_idM]
  let g : Fin 6 → GL (Fin 42) (ZMod 3) := fun i =>
    ⟨toMat 42 (E i.val), toMat 42 (Ei i.val), hinv1 i, hinv2 i⟩
  have hg : ∀ i : Fin 6, toMat 42 (E i.val) = ((g i : GL (Fin 42) (ZMod 3)) :
      Matrix (Fin 42) (Fin 42) (ZMod 3)) := fun i => rfl
  have hgi : ∀ i : Fin 6, toMat 42 (Ei i.val) = (((g i)⁻¹ : GL (Fin 42) (ZMod 3)) :
      Matrix (Fin 42) (Fin 42) (ZMod 3)) := fun i => rfl
  have hval := toMat_mclEvalM E Ei g hE hEi hg hgi
  have hrel : ∀ r ∈ coverRelators (wordSet mclRels) mclCommW, FreeGroup.lift g r = 1 := by
    intro r hr
    rw [coverRelators_mclCommW] at hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    apply Units.ext
    rw [← hval w, toMat_eq_of_eqM (hcov w hw), toMat_idM, Units.val_one]
  have hZw := mclEvalM_facts E Ei hE hEi mclR0
  have hmk : (PresentedGroup.toGroup hrel) (PresentedGroup.mk _ (FreeGroup.mk mclR0)) =
      FreeGroup.lift g (FreeGroup.mk mclR0) := rfl
  refine ⟨PresentedGroup.toGroup hrel, ?_, ?_⟩
  · intro h1
    rw [hmk] at h1
    have h3 := congrArg (fun x : GL (Fin 42) (ZMod 3) => (x : Matrix (Fin 42) (Fin 42) (ZMod 3))) h1
    simp only [Units.val_one] at h3
    exact not_eqM_of_ne hZw.1 hZne hZc (canonM_idM 42) (((hval mclR0).trans h3).trans
      (toMat_idM 42).symm)
  · rw [hmk]
    have hZZ : (mul 42 (mclEvalM E Ei mclR0) (mclEvalM E Ei mclR0)).size = 42 ∧
        RowsWF (mul 42 (mclEvalM E Ei mclR0) (mclEvalM E Ei mclR0)) :=
      ⟨(mul_size 42 _ _).trans hZw.1, RowsWF.mul _ 42 hZw.2 hZw.2⟩
    apply Units.ext
    rw [pow_three, Units.val_mul, Units.val_mul, ← hval mclR0, ← toMat_mul hZw.1 hZw.2 hZw.2,
      ← toMat_mul hZw.1 hZw.2 hZZ.2, toMat_eq_of_eqM hZ3, toMat_idM, Units.val_one]

end CFSG.Sporadic.Recognition.McLMultiplier
