module

public import CFSG.RankThree.PartOne.CTP.ExtA
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped MatrixGroups

theorem psl2_model_noncomm {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) : ∃ x y : X, x * y ≠ y * x := by
  obtain ⟨L, _, _, _, -, ⟨e⟩⟩ := exists_sl2_equiv_of_model h
  let x : SL(2, L) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let y : SL(2, L) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨e x, e y, fun hxy => ?_⟩
  have h1 : x * y = y * x := e.injective (by rw [map_mul, map_mul]; exact hxy)
  have h2 := congrArg (fun m : SL(2, L) => (m : Matrix (Fin 2) (Fin 2) L) 0 0) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h2
  simp [x, y, Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem psl2_model_center_eq_bot {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) : Subgroup.center X = ⊥ := by
  obtain ⟨x, y, hxy⟩ := psl2_model_noncomm h
  have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 f h).2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h0 | h1
  · exact h0
  · exfalso
    have hx : x ∈ Subgroup.center X := by rw [h1]; trivial
    exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)

theorem psl2_model_exists_noncomm {X : Type} [Group X] {f : ℕ} {J : Subgroup X}
    (h : StatedClassicalModel ↥J .PSL 2 2 f) : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := psl2_model_noncomm h
  exact ⟨x, x.2, y, y.2, fun h' => hxy (Subtype.ext h')⟩

end CFSG.RankThree.PartOne.CTP
