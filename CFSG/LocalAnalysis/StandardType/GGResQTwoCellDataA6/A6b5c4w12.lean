module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.Common

public section

namespace CFSG.StandardType.GGResQTwoCellDataA6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def w_A6b5c4w12_0_0 : GGResQTwoCell 6 :=
  .commonKernel [1, 2, 0, 1, 2, 1, 1]

@[expose] def w_A6b5c4w12_0_1 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.A6b5c4w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A6b5c4w12_0_2 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.A6b5c4w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A6b5c4w12_1_0 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.A6b5c4w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A6b5c4w12_1_1 : GGResQTwoCell 6 :=
  .commonKernel [0, 0, 0, 0, 0, 1, 1]

@[expose] def w_A6b5c4w12_1_2 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.A6b5c4w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A6b5c4w12_2_0 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.A6b5c4w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A6b5c4w12_2_1 : GGResQTwoCell 6 :=
  .norm [0, 1, 2, 3, 4, 5] [0, 0, 0, 0, 0, 1, 1] Rq2_2cce17e5c6cf7fa5 [6, 4, 3, 5, 4, 6, 4, 5, 3, 4, 6] 2

@[expose] def w_A6b5c4w12_2_2 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.A6b5c4w12.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A6b5c4w12_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 6) 5 4 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5] Rq2_2cce17e5c6cf7fa5 [0, 0, 0, 0, 0, 1, 1] [6, 4, 3, 5, 4, 6, 4, 5, 3, 4, 6] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA6) (by decide +kernel)
    (by decide +kernel) (pkListA6 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A6b5c4w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_A6b5c4w12_0_0) = true := by
  rw [show w_A6b5c4w12_0_0 = .commonKernel [1, 2, 0, 1, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 1, 2, 1, 1]) (by decide +kernel)

theorem hcell_A6b5c4w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_A6b5c4w12_0_1) = true := by
  rw [show w_A6b5c4w12_0_1 = .reuse ((GGResIShape.A6b5c4w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A6b5c4w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A6b5c4w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A6b5c4w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A6b5c4w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_A6b5c4w12_0_2) = true := by
  rw [show w_A6b5c4w12_0_2 = .reuse ((GGResIShape.A6b5c4w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A6b5c4w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A6b5c4w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A6b5c4w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A6b5c4w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_A6b5c4w12_1_0) = true := by
  rw [show w_A6b5c4w12_1_0 = .reuse ((GGResIShape.A6b5c4w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A6b5c4w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A6b5c4w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A6b5c4w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A6b5c4w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_A6b5c4w12_1_1) = true := by
  rw [show w_A6b5c4w12_1_1 = .commonKernel [0, 0, 0, 0, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 0, 0, 1, 1]) (by decide +kernel)

theorem hcell_A6b5c4w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_A6b5c4w12_1_2) = true := by
  rw [show w_A6b5c4w12_1_2 = .reuse ((GGResIShape.A6b5c4w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A6b5c4w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A6b5c4w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A6b5c4w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A6b5c4w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_A6b5c4w12_2_0) = true := by
  rw [show w_A6b5c4w12_2_0 = .reuse ((GGResIShape.A6b5c4w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A6b5c4w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A6b5c4w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A6b5c4w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A6b5c4w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_A6b5c4w12_2_1) = true := by
  rw [show w_A6b5c4w12_2_1 = .norm [0, 1, 2, 3, 4, 5] [0, 0, 0, 0, 0, 1, 1] Rq2_2cce17e5c6cf7fa5 [6, 4, 3, 5, 4, 6, 4, 5, 3, 4, 6] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5] [0, 0, 0, 0, 0, 1, 1] Rq2_2cce17e5c6cf7fa5 [6, 4, 3, 5, 4, 6, 4, 5, 3, 4, 6] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A6b5c4w12_2_1

theorem hcell_A6b5c4w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 6) 5 4 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_A6b5c4w12_2_2) = true := by
  rw [show w_A6b5c4w12_2_2 = .reuse ((GGResIShape.A6b5c4w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A6b5c4w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A6b5c4w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A6b5c4w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_A6b5c4w12 : List (ℕ × ℕ × GGResQTwoCell 6) :=
  [(0, 0, w_A6b5c4w12_0_0), (0, 1, w_A6b5c4w12_0_1), (0, 2, w_A6b5c4w12_0_2), (1, 0, w_A6b5c4w12_1_0), (1, 1, w_A6b5c4w12_1_1), (1, 2, w_A6b5c4w12_1_2), (2, 0, w_A6b5c4w12_2_0), (2, 1, w_A6b5c4w12_2_1), (2, 2, w_A6b5c4w12_2_2)]

theorem hwits_A6b5c4w12 :
    GGResQTwoCellCheckAll (CartanMatrix.A 6) 5 4 (-1) (-2) wits_A6b5c4w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_0_0) (by rfl)]
      exact hcell_A6b5c4w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_0_1) (by rfl)]
      exact hcell_A6b5c4w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_0_2) (by rfl)]
      exact hcell_A6b5c4w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_1_0) (by rfl)]
      exact hcell_A6b5c4w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_1_1) (by rfl)]
      exact hcell_A6b5c4w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_1_2) (by rfl)]
      exact hcell_A6b5c4w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_2_0) (by rfl)]
      exact hcell_A6b5c4w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_2_1) (by rfl)]
      exact hcell_A6b5c4w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A6b5c4w12_2_2) (by rfl)]
      exact hcell_A6b5c4w12_2_2

end CFSG.StandardType.GGResQTwoCellDataA6
