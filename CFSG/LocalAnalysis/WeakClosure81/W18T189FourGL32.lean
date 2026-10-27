module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace GL32Fix

open Matrix
open scoped MatrixGroups

private abbrev glf_Mat3 := Matrix (Fin 3) (Fin 3) (ZMod 2)

private lemma glf_coe_mkOfDetNeZero (M : glf_Mat3) (h : M.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero M h : GL (Fin 3) (ZMod 2)) : glf_Mat3) = M :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero M h

private lemma glf_natCard_eq_card_of_finset (p : glf_Mat3 → Prop) (S : Finset glf_Mat3)
    (h1 : ∀ g : GL (Fin 3) (ZMod 2), p (g : glf_Mat3) → (g : glf_Mat3) ∈ S)
    (h2 : ∀ M ∈ S, p M ∧ M.det ≠ 0) :
    Nat.card {g : GL (Fin 3) (ZMod 2) // p (g : glf_Mat3)} = S.card := by
  have hinj : Function.Injective
      (fun g : {g : GL (Fin 3) (ZMod 2) // p (g : glf_Mat3)} => (g.1 : glf_Mat3)) :=
    fun a b hab => Subtype.ext (Units.ext hab)
  have hr : Set.range (fun g : {g : GL (Fin 3) (ZMod 2) // p (g : glf_Mat3)} =>
      (g.1 : glf_Mat3)) = (S : Set glf_Mat3) := by
    ext M
    constructor
    · rintro ⟨g, rfl⟩
      exact h1 g.1 g.2
    · intro hM
      obtain ⟨hMp, hMdet⟩ := h2 M hM
      refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet, ?_⟩, ?_⟩
      · rw [glf_coe_mkOfDetNeZero]
        exact hMp
      · rfl
  rw [← Nat.card_range_of_injective hinj, hr, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private lemma glf_card_filter_col :
    ∀ u : Fin 3 → ZMod 2, u ≠ 0 →
      (Finset.univ.filter fun M : glf_Mat3 => M.det ≠ 0 ∧ Matrix.mulVec M u = u).card = 24 := by
  decide +kernel

private lemma glf_card_filter_row :
    ∀ w : Fin 3 → ZMod 2, w ≠ 0 →
      (Finset.univ.filter fun M : glf_Mat3 => M.det ≠ 0 ∧ Matrix.vecMul w M = w).card = 24 := by
  decide +kernel

private lemma glf_exists_col_not_row_mat :
    ∀ u w : Fin 3 → ZMod 2, u ≠ 0 → w ≠ 0 →
      ∃ M : glf_Mat3, M.det ≠ 0 ∧ Matrix.mulVec M u = u ∧ Matrix.vecMul w M ≠ w := by
  decide +kernel

private lemma glf_exists_row_not_col_mat :
    ∀ w u : Fin 3 → ZMod 2, w ≠ 0 → u ≠ 0 →
      ∃ M : glf_Mat3, M.det ≠ 0 ∧ Matrix.vecMul w M = w ∧ Matrix.mulVec M u ≠ u := by
  decide +kernel

private def glf_colFix (x y : glf_Mat3) : ℕ :=
  (Finset.univ.filter fun u : Fin 3 → ZMod 2 =>
    Matrix.mulVec x u = u ∧ Matrix.mulVec y u ≠ u).card

private def glf_rowFix (x y : glf_Mat3) : ℕ :=
  (Finset.univ.filter fun w : Fin 3 → ZMod 2 =>
    Matrix.vecMul w x = w ∧ Matrix.vecMul w y ≠ w).card

private lemma glf_colFix_pos_iff (x y : glf_Mat3) :
    0 < glf_colFix x y ↔ ∃ u : Fin 3 → ZMod 2,
      Matrix.mulVec x u = u ∧ Matrix.mulVec y u ≠ u := by
  rw [glf_colFix, Finset.card_pos]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (Finset.mem_filter.mp hu).2⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩

private lemma glf_rowFix_pos_iff (x y : glf_Mat3) :
    0 < glf_rowFix x y ↔ ∃ w : Fin 3 → ZMod 2,
      Matrix.vecMul w x = w ∧ Matrix.vecMul w y ≠ w := by
  rw [glf_rowFix, Finset.card_pos]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩

private lemma glf_exists_klein_mat :
    ∀ x y : glf_Mat3, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x ≠ y → x * y = y * x →
      0 < glf_colFix x y ∨ 0 < glf_rowFix x y := by
  decide +kernel

theorem card_col (u : Fin 3 → ZMod 2) (hu : u ≠ 0) :
    Nat.card {M : GL (Fin 3) (ZMod 2) //
      Matrix.mulVec (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) u = u} = 24 := by
  rw [glf_natCard_eq_card_of_finset (fun M : glf_Mat3 => Matrix.mulVec M u = u)
    (Finset.univ.filter fun M : glf_Mat3 => M.det ≠ 0 ∧ Matrix.mulVec M u = u)]
  · exact glf_card_filter_col u hu
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Matrix.GeneralLinearGroup.det_ne_zero g, hg⟩
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    exact ⟨hM.2, hM.1⟩

theorem card_row (w : Fin 3 → ZMod 2) (hw : w ≠ 0) :
    Nat.card {M : GL (Fin 3) (ZMod 2) //
      Matrix.vecMul w (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) = w} = 24 := by
  rw [glf_natCard_eq_card_of_finset (fun M : glf_Mat3 => Matrix.vecMul w M = w)
    (Finset.univ.filter fun M : glf_Mat3 => M.det ≠ 0 ∧ Matrix.vecMul w M = w)]
  · exact glf_card_filter_row w hw
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Matrix.GeneralLinearGroup.det_ne_zero g, hg⟩
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    exact ⟨hM.2, hM.1⟩

theorem exists_col_not_row (u w : Fin 3 → ZMod 2) (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ M : GL (Fin 3) (ZMod 2), Matrix.mulVec (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) u = u ∧
      Matrix.vecMul w (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ w := by
  obtain ⟨M, hdet, hMu, hwM⟩ := glf_exists_col_not_row_mat u w hu hw
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · rw [glf_coe_mkOfDetNeZero]
    exact hMu
  · rw [glf_coe_mkOfDetNeZero]
    exact hwM

theorem exists_row_not_col (w u : Fin 3 → ZMod 2) (hw : w ≠ 0) (hu : u ≠ 0) :
    ∃ M : GL (Fin 3) (ZMod 2), Matrix.vecMul w (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) = w ∧
      Matrix.mulVec (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) u ≠ u := by
  obtain ⟨M, hdet, hwM, hMu⟩ := glf_exists_row_not_col_mat w u hw hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · rw [glf_coe_mkOfDetNeZero]
    exact hwM
  · rw [glf_coe_mkOfDetNeZero]
    exact hMu

theorem exists_klein (x y : GL (Fin 3) (ZMod 2)) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hc : x * y = y * x) :
    (∃ u : Fin 3 → ZMod 2, Matrix.mulVec (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) u = u ∧
        Matrix.mulVec (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) u ≠ u) ∨
      ∃ w : Fin 3 → ZMod 2, Matrix.vecMul w (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = w ∧
        Matrix.vecMul w (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ w := by
  have hx2' : (x : glf_Mat3) * (x : glf_Mat3) = 1 := by
    simpa using congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : glf_Mat3)) hx2
  have hy2' : (y : glf_Mat3) * (y : glf_Mat3) = 1 := by
    simpa using congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : glf_Mat3)) hy2
  have hx1' : (x : glf_Mat3) ≠ 1 := fun h => hx1 (Units.ext h)
  have hy1' : (y : glf_Mat3) ≠ 1 := fun h => hy1 (Units.ext h)
  have hxy' : (x : glf_Mat3) ≠ (y : glf_Mat3) := fun h => hxy (Units.ext h)
  have hc' : (x : glf_Mat3) * (y : glf_Mat3) = (y : glf_Mat3) * (x : glf_Mat3) := by
    simpa using congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : glf_Mat3)) hc
  rcases glf_exists_klein_mat (x : glf_Mat3) (y : glf_Mat3) hx2' hy2' hx1' hy1' hxy' hc' with h | h
  · left
    exact (glf_colFix_pos_iff _ _).mp h
  · right
    exact (glf_rowFix_pos_iff _ _).mp h

end GL32Fix

end CFSG.LocalAnalysis.WeakClosure81

end
