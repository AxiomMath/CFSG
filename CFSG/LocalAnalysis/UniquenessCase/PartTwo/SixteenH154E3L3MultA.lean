module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup Matrix

theorem s16h_e3_mul_eq_right_of_commute_left
    (T : Matrix (Fin 3) (Fin 3) (ZMod 2) →+ Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hT : ∀ (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))
        (X : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      T ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X) =
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * T X)
    (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) : T X = X * T 1 := by
  have hE : ∀ i j : Fin 3, i ≠ j →
      T (Matrix.single i j (1 : ZMod 2)) = Matrix.single i j (1 : ZMod 2) * T 1 := by
    intro i j hij
    let A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
      Matrix.GeneralLinearGroup.transvection i j hij 1
    have hcoe : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        1 + Matrix.single i j (1 : ZMod 2) := by
      simp [A, Matrix.GeneralLinearGroup.transvection, Matrix.transvection]
    have h := hT A 1
    rw [Matrix.mul_one, hcoe, map_add, Matrix.add_mul, Matrix.one_mul] at h
    exact add_left_cancel h
  have hdiag : ∀ i : Fin 3,
      T (Matrix.single i i (1 : ZMod 2)) = Matrix.single i i (1 : ZMod 2) * T 1 := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Fin 3, j ≠ i := by
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    have hij : i ≠ j := Ne.symm hji
    let A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
      Matrix.GeneralLinearGroup.transvection i j hij 1
    have hcoe : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        1 + Matrix.single i j (1 : ZMod 2) := by
      simp [A, Matrix.GeneralLinearGroup.transvection, Matrix.transvection]
    have h := hT A (Matrix.single j i (1 : ZMod 2))
    rw [hcoe, hE j i hji] at h
    have hmul : (1 + Matrix.single i j (1 : ZMod 2)) * Matrix.single j i (1 : ZMod 2) =
        Matrix.single j i (1 : ZMod 2) + Matrix.single i i (1 : ZMod 2) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.single_mul_single_same, one_mul]
    rw [hmul, map_add] at h
    rw [hE j i hji] at h
    have hrhs : (1 + Matrix.single i j (1 : ZMod 2)) * (Matrix.single j i (1 : ZMod 2) * T 1) =
        Matrix.single j i (1 : ZMod 2) * T 1 + Matrix.single i i (1 : ZMod 2) * T 1 := by
      rw [Matrix.add_mul, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.single_mul_single_same,
        one_mul]
    rw [hrhs] at h
    exact add_left_cancel h
  refine Matrix.induction_on' X ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [map_add, hp, hq, Matrix.add_mul]
  · intro i j x
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl
    · simp
    · by_cases hij : i = j
      · subst hij
        exact hdiag i
      · exact hE i j hij

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
