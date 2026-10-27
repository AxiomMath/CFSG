module

public import CFSG.RankThree.PartOne.KF4.ShortA2Native

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups

section Rep

variable {K : Type} [Field K]

@[expose] def symRep (K : Type) [Field K] : SL(3, K) →* Matrix (Fin 6) (Fin 6) K where
  toFun A := symCong (A : Matrix (Fin 3) (Fin 3) K)
  map_one' := by simpa using symCong_one
  map_mul' A B := by
    simpa using symCong_mul (A : Matrix (Fin 3) (Fin 3) K) B

theorem symRep_apply (A : SL(3, K)) : symRep K A = symCong (A : Matrix (Fin 3) (Fin 3) K) := rfl

theorem symRep_injective : Function.Injective (symRep K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  exact Subtype.ext (eq_one_of_symCong_eq_one hA A.2)

theorem symCong_elem (i j : Fin 3) (hij : i ≠ j) (t : K) :
    symCong (1 - t • single i j 1) =
      symRep K (Matrix.SpecialLinearGroup.transvection hij (-t)) := by
  rw [symRep_apply, CFSG.LinearGroups.coe_transvection]
  congr 1
  rw [sub_eq_add_neg, Matrix.smul_single, Matrix.single_neg]
  simp

theorem exists_symRep {g : ModGL Tag.F4 K} (hg : g ∈ subsystemGroup Tag.F4 K f4ShortSupport) :
    ∃ A : SL(3, K), f4Short_data.Mat g = symRep K A := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_f4ShortSupport i).1 hi with rfl | rfl
      · exact ⟨_, by rw [f4Short_Mat_x3, f4ShortX3_eq, symCong_elem (K := K) 1 0 (by decide)]⟩
      · exact ⟨_, by rw [f4Short_Mat_x4, f4ShortX4_eq, symCong_elem (K := K) 2 1 (by decide)]⟩
    · rcases (mem_f4ShortSupport i).1 hi with rfl | rfl
      · exact ⟨_, by rw [f4Short_Mat_y3, f4ShortY3_eq, symCong_elem (K := K) 0 1 (by decide)]⟩
      · exact ⟨_, by rw [f4Short_Mat_y4, f4ShortY4_eq, symCong_elem (K := K) 1 2 (by decide)]⟩
  | one => exact ⟨1, by rw [f4Short_data.Mat_one, map_one]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨A, hA⟩ := ihx
    obtain ⟨B, hB⟩ := ihy
    exact ⟨A * B, by rw [f4Short_data.Mat_mul hx hy, hA, hB, map_mul]⟩
  | inv x hx ih =>
    obtain ⟨A, hA⟩ := ih
    refine ⟨A⁻¹, ?_⟩
    rw [f4Short_data.Mat_inv hx, hA]
    refine Matrix.inv_eq_right_inv ?_
    rw [← map_mul, mul_inv_cancel, map_one]

end Rep

end CFSG.RankThree.PartOne.KF4
