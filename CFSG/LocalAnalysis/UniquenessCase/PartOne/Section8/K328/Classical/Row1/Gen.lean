module

import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

private theorem k328r1g_transvection_comm {F : Type} [Field F] {d : Fin 4 → F} {i j : Fin 4}
    (hd : d i = d j) (c : F) :
    (1 + Matrix.single i j c) * Matrix.diagonal d =
      Matrix.diagonal d * (1 + Matrix.single i j c) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : a = b
  · subst hab
    exact mul_comm _ _
  · by_cases h : i = a ∧ j = b
    · rw [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply, if_pos h,
        ← h.1, ← h.2, hd]
      exact mul_comm _ _
    · rw [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply, if_neg h,
        zero_mul, mul_zero]

private theorem k328r1g_mem {F : Type} [Field F] {s : GL (Fin 4) F} {d : Fin 4 → F}
    (hs : (s : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d) {i j : Fin 4} (hij : i ≠ j)
    (hd : d i = d j) (c : F) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c) ∈
      StatedSL 4 F ⊓ Subgroup.centralizer {s} := by
  refine ⟨?_, ?_⟩
  · rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
    exact ⟨_, rfl⟩
  · show _ ∈ Subgroup.centralizer {s}
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hs, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.transvection_coe]
    exact k328r1g_transvection_comm hd c

private theorem k328r1g_le_of_transvection {F : Type} [Field F] (J : Subgroup (GL (Fin 4) F))
    (h : ∀ (i j : Fin 4) (hij : i ≠ j) (c : F),
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c) ∈ J) :
    StatedSL 4 F ≤ J := by
  intro g hg
  rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL] at hg
  obtain ⟨x, rfl⟩ := hg
  have htop := CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
    (J.comap Matrix.SpecialLinearGroup.toGL) h
  have hx : x ∈ J.comap Matrix.SpecialLinearGroup.toGL := by
    rw [htop]
    exact Subgroup.mem_top x
  exact hx

private theorem k328r1g_zt {F : Type} [Field F] {ω : F} (hω3 : ω ^ 3 = 1) {z₀ t₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    ((z₀ * t₀ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![ω ^ 2, 1, ω, 1] := by
  rw [Units.val_mul, hz, ht, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · show ω * ω = ω ^ 2
    ring1
  · show ω * ω ^ 2 = 1
    linear_combination hω3
  · show ω * 1 = ω
    ring1
  · show 1 * 1 = 1
    ring1

private theorem k328r1g_ztt {F : Type} [Field F] {ω : F} (hω3 : ω ^ 3 = 1)
    {z₀ t₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    ((z₀ * t₀ ^ 2 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![1, ω ^ 2, ω, 1] := by
  rw [pow_two t₀, Units.val_mul, Units.val_mul, hz, ht, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · show ω * (ω * ω) = 1
    linear_combination hω3
  · show ω * (ω ^ 2 * ω ^ 2) = ω ^ 2
    linear_combination ω ^ 2 * hω3
  · show ω * (1 * 1) = ω
    ring1
  · show 1 * (1 * 1) = 1
    ring1

theorem row1_gen (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    GenLeaf (StatedSL 4 F) z₀ t₀ := by
  have _ := hF
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hzt := k328r1g_zt hω3 hz ht
  have hztt := k328r1g_ztt hω3 hz ht
  unfold GenLeaf
  refine le_antisymm (sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left) inf_le_left)
    (k328r1g_le_of_transvection _ fun i j hij c => ?_)
  fin_cases i <;> fin_cases j <;>
    first
      | exact (hij rfl).elim
      | exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (k328r1g_mem hz hij rfl c)))
      | exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (k328r1g_mem ht hij rfl c)))
      | exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (k328r1g_mem hzt hij rfl c))
      | exact Subgroup.mem_sup_right (k328r1g_mem hztt hij rfl c)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
