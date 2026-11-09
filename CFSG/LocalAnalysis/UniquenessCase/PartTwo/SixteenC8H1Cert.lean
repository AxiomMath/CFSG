module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Fox

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin.JonesParshall

@[expose] def bitMat (r : Fin 8 → ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if (r i).testBit j then 1 else 0

@[expose] def genRowsP : Fin 8 → Fin 8 → ℕ :=
  ![![3, 2, 4, 8, 144, 32, 64, 128],
    ![5, 2, 4, 8, 16, 160, 64, 128],
    ![9, 2, 4, 8, 16, 32, 192, 128],
    ![17, 130, 4, 8, 16, 40, 68, 128],
    ![33, 2, 132, 8, 24, 32, 66, 128],
    ![65, 2, 4, 136, 20, 34, 64, 128],
    ![1, 2, 4, 10, 80, 32, 64, 128],
    ![1, 4, 8, 2, 32, 64, 16, 128]]

@[expose] def matsP : Fin 8 → Matrix (Fin 8) (Fin 8) (ZMod 2) := fun j => bitMat (genRowsP j)

@[expose] def relsP : Fin 10 → List (Fin 8) :=
  ![[5, 5],
    [7, 7, 7],
    [6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7],
    [6, 2, 6, 0, 2],
    [6, 3, 6, 1, 3, 5],
    [6, 4, 6, 4],
    [7, 1, 7, 7, 0],
    [7, 2, 7, 7, 1],
    [7, 4, 7, 7, 3],
    [7, 5, 7, 7, 4]]

@[expose] def certPRows : Fin 8 → Fin 8 → ℕ :=
  ![![0, 1, 0, 0, 0, 0, 0, 16],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]]

@[expose] def certCRows : Fin 8 → Fin 10 → Fin 8 → ℕ :=
  ![![![0, 0, 0, 40, 0, 0, 8, 0],
      ![0, 0, 0, 130, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 128, 0],
      ![0, 2, 4, 0, 0, 32, 192, 128],
      ![0, 0, 0, 130, 0, 0, 128, 0],
      ![0, 0, 0, 4, 0, 0, 0, 0],
      ![0, 0, 0, 8, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 128, 0],
      ![0, 0, 0, 128, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 40, 16, 0, 8, 0, 0, 8],
      ![0, 128, 0, 2, 16, 16, 16, 0],
      ![0, 0, 0, 0, 128, 0, 0, 0],
      ![0, 0, 0, 4, 192, 128, 32, 0],
      ![0, 130, 4, 0, 128, 0, 0, 128],
      ![0, 4, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 4, 64, 16, 32, 0],
      ![0, 0, 0, 0, 128, 0, 0, 0],
      ![0, 128, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 40, 16, 0, 8, 8, 8],
      ![0, 0, 130, 2, 0, 0, 0, 128],
      ![0, 0, 0, 0, 0, 128, 0, 0],
      ![0, 4, 0, 0, 32, 192, 128, 0],
      ![0, 0, 130, 4, 0, 128, 128, 128],
      ![0, 0, 4, 0, 0, 0, 0, 0],
      ![0, 4, 0, 0, 32, 64, 16, 0],
      ![0, 8, 2, 4, 64, 144, 32, 128],
      ![0, 0, 128, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 25, 32, 40, 1, 0, 1, 0],
      ![0, 2, 0, 128, 0, 16, 147, 0],
      ![0, 0, 0, 0, 0, 128, 128, 128],
      ![0, 104, 0, 12, 0, 17, 225, 0],
      ![0, 240, 0, 130, 0, 2, 86, 0],
      ![0, 20, 0, 12, 0, 28, 28, 4],
      ![0, 120, 0, 12, 0, 25, 105, 0],
      ![0, 136, 0, 8, 0, 37, 132, 0],
      ![0, 204, 4, 136, 16, 168, 128, 128],
      ![0, 88, 8, 0, 32, 8, 72, 0]],
    ![![0, 40, 25, 32, 49, 1, 56, 0],
      ![0, 130, 0, 2, 130, 16, 128, 128],
      ![0, 0, 128, 0, 128, 0, 128, 128],
      ![0, 12, 104, 0, 225, 0, 31, 0],
      ![0, 130, 240, 0, 82, 0, 132, 0],
      ![0, 12, 16, 0, 28, 0, 16, 4],
      ![0, 12, 120, 0, 105, 0, 20, 0],
      ![0, 8, 136, 0, 133, 0, 44, 0],
      ![0, 128, 78, 0, 196, 0, 0, 0],
      ![0, 0, 88, 8, 64, 32, 8, 0]],
    ![![0, 32, 16, 49, 16, 1, 1, 8],
      ![0, 0, 0, 2, 19, 144, 0, 0],
      ![0, 0, 0, 0, 128, 128, 0, 0],
      ![0, 0, 0, 96, 17, 227, 0, 0],
      ![0, 0, 0, 250, 6, 86, 0, 0],
      ![0, 0, 0, 20, 28, 28, 0, 0],
      ![0, 0, 0, 112, 25, 104, 0, 0],
      ![0, 0, 0, 128, 36, 132, 0, 0],
      ![0, 0, 0, 204, 128, 196, 0, 0],
      ![0, 0, 0, 88, 72, 88, 0, 0]],
    ![![0, 40, 49, 56, 41, 1, 8, 0],
      ![1, 130, 16, 128, 147, 16, 128, 128],
      ![1, 0, 0, 0, 0, 0, 128, 128],
      ![0, 12, 32, 3, 1, 0, 16, 0],
      ![0, 130, 68, 134, 215, 0, 128, 0],
      ![0, 4, 0, 4, 28, 1, 0, 0],
      ![0, 12, 32, 8, 9, 0, 16, 0],
      ![0, 8, 0, 4, 4, 0, 32, 0],
      ![0, 128, 4, 128, 148, 0, 0, 0],
      ![0, 0, 8, 0, 96, 32, 0, 0]],
    ![![0, 0, 16, 16, 1, 1, 0, 0],
      ![1, 3, 3, 2, 17, 1, 0, 128],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 2, 0, 2, 0, 0, 0, 0],
      ![0, 0, 4, 4, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 1, 0, 0, 0, 0],
      ![0, 0, 1, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 17, 0, 17, 0],
      ![0, 0, 0, 0, 32, 33, 1, 0]]]

theorem relsP_spec : ∀ r, wordEvalM matsP (relsP r) = 1 := by
  decide +kernel

@[expose] def foxTabP : Fin 10 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![64, 0, 0, 128, 4, 2, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 14, 14, 14, 112, 112, 112, 128]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 128],
      ![1, 0, 0, 0, 0, 0, 0, 128]],
    ![![11, 2, 4, 8, 144, 32, 192, 128],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![8, 0, 0, 2, 64, 0, 128, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![8, 0, 0, 2, 192, 0, 128, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![81, 130, 4, 136, 20, 42, 68, 128],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![84, 128, 0, 130, 68, 138, 4, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![65, 2, 4, 136, 20, 34, 64, 128],
      ![16, 128, 0, 130, 68, 8, 4, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![32, 0, 128, 2, 72, 0, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![32, 0, 128, 2, 74, 0, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![3, 2, 4, 8, 144, 32, 64, 128],
      ![1, 4, 8, 2, 32, 64, 16, 128],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![13, 14, 14, 14, 112, 112, 112, 128]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![5, 2, 4, 8, 16, 160, 64, 128],
      ![1, 4, 8, 2, 32, 64, 16, 128],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![11, 14, 14, 14, 112, 112, 112, 128]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![17, 130, 4, 8, 16, 40, 68, 128],
      ![1, 4, 8, 2, 32, 64, 16, 128],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![97, 14, 14, 14, 112, 118, 122, 128]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![33, 2, 132, 8, 24, 32, 66, 128],
      ![1, 4, 8, 2, 32, 64, 16, 128],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![81, 14, 14, 14, 118, 112, 124, 128]]]

private theorem foxP_eq_0 : ∀ l : Fin 8, foxCoefM matsP (relsP 0) l = bitMat (foxTabP 0 l) := by
  decide +kernel

private theorem foxP_eq_1 : ∀ l : Fin 8, foxCoefM matsP (relsP 1) l = bitMat (foxTabP 1 l) := by
  decide +kernel

private theorem foxP_eq_2 : ∀ l : Fin 8, foxCoefM matsP (relsP 2) l = bitMat (foxTabP 2 l) := by
  decide +kernel

private theorem foxP_eq_3 : ∀ l : Fin 8, foxCoefM matsP (relsP 3) l = bitMat (foxTabP 3 l) := by
  decide +kernel

private theorem foxP_eq_4 : ∀ l : Fin 8, foxCoefM matsP (relsP 4) l = bitMat (foxTabP 4 l) := by
  decide +kernel

private theorem foxP_eq_5 : ∀ l : Fin 8, foxCoefM matsP (relsP 5) l = bitMat (foxTabP 5 l) := by
  decide +kernel

private theorem foxP_eq_6 : ∀ l : Fin 8, foxCoefM matsP (relsP 6) l = bitMat (foxTabP 6 l) := by
  decide +kernel

private theorem foxP_eq_7 : ∀ l : Fin 8, foxCoefM matsP (relsP 7) l = bitMat (foxTabP 7 l) := by
  decide +kernel

private theorem foxP_eq_8 : ∀ l : Fin 8, foxCoefM matsP (relsP 8) l = bitMat (foxTabP 8 l) := by
  decide +kernel

private theorem foxP_eq_9 : ∀ l : Fin 8, foxCoefM matsP (relsP 9) l = bitMat (foxTabP 9 l) := by
  decide +kernel

theorem foxP_eq : ∀ r l, foxCoefM matsP (relsP r) l = bitMat (foxTabP r l) := by
  intro r
  fin_cases r
  exacts [foxP_eq_0, foxP_eq_1, foxP_eq_2, foxP_eq_3, foxP_eq_4, foxP_eq_5, foxP_eq_6, foxP_eq_7,
    foxP_eq_8, foxP_eq_9]

private theorem certP_spec_0 : ∀ l : Fin 8,
    (if (0 : Fin 8) = l then 1 else 0) - (matsP 0 - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows 0 r) * bitMat (foxTabP r l) := by
  decide +kernel

private theorem certP_spec_1 : ∀ l : Fin 8,
    (if (1 : Fin 8) = l then 1 else 0) - (matsP 1 - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows 1 r) * bitMat (foxTabP r l) := by
  decide +kernel

private theorem certP_spec_2 : ∀ l : Fin 8,
    (if (2 : Fin 8) = l then 1 else 0) - (matsP 2 - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows 2 r) * bitMat (foxTabP r l) := by
  decide +kernel

private theorem certP_spec_3 : ∀ l : Fin 8,
    (if (3 : Fin 8) = l then 1 else 0) - (matsP 3 - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows 3 r) * bitMat (foxTabP r l) := by
  decide +kernel

private theorem certP_spec_4 : ∀ l : Fin 8,
    (if (4 : Fin 8) = l then 1 else 0) - (matsP 4 - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows 4 r) * bitMat (foxTabP r l) := by
  decide +kernel

private theorem certP_spec_5 : ∀ l : Fin 8,
    (if (5 : Fin 8) = l then 1 else 0) - (matsP 5 - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows 5 r) * bitMat (foxTabP r l) := by
  decide +kernel

private theorem certP_spec_6 : ∀ l : Fin 8,
    (if (6 : Fin 8) = l then 1 else 0) - (matsP 6 - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows 6 r) * bitMat (foxTabP r l) := by
  decide +kernel

private theorem certP_spec_7 : ∀ l : Fin 8,
    (if (7 : Fin 8) = l then 1 else 0) - (matsP 7 - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows 7 r) * bitMat (foxTabP r l) := by
  decide +kernel

theorem certP_spec : ∀ j l : Fin 8,
    (if j = l then 1 else 0) - (matsP j - 1) * bitMat (certPRows l) =
      ∑ r, bitMat (certCRows j r) * foxCoefM matsP (relsP r) l := by
  intro j
  simp only [foxP_eq]
  fin_cases j
  · exact certP_spec_0
  · exact certP_spec_1
  · exact certP_spec_2
  · exact certP_spec_3
  · exact certP_spec_4
  · exact certP_spec_5
  · exact certP_spec_6
  · exact certP_spec_7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
