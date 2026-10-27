module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B3
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData

public section

namespace CFSG.StandardType.GGResQTwoCellDataB3

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def w_B3b0c2_0_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b0c2.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_B3b0c2_0_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b0c2.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_B3b0c2_0_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b0c2.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_B3b0c2_1_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b0c2.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_B3b0c2_1_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b0c2.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_B3b0c2_1_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b0c2.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_B3b0c2_2_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b0c2.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_B3b0c2_2_1 : GGResQTwoCell 3 :=
  .residual .B3b0c2

@[expose] def w_B3b0c2_2_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b0c2.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_B3b0c2_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_B3b0c2_0_0) = true := by
  rw [show w_B3b0c2_0_0 = .reuse ((GGResIShape.B3b0c2.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b0c2.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b0c2.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b0c2_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_B3b0c2_0_1) = true := by
  rw [show w_B3b0c2_0_1 = .reuse ((GGResIShape.B3b0c2.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b0c2.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b0c2.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b0c2_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_B3b0c2_0_2) = true := by
  rw [show w_B3b0c2_0_2 = .reuse ((GGResIShape.B3b0c2.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b0c2.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b0c2.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b0c2_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_B3b0c2_1_0) = true := by
  rw [show w_B3b0c2_1_0 = .reuse ((GGResIShape.B3b0c2.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b0c2.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b0c2.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b0c2_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_B3b0c2_1_1) = true := by
  rw [show w_B3b0c2_1_1 = .reuse ((GGResIShape.B3b0c2.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b0c2.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b0c2.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b0c2_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_B3b0c2_1_2) = true := by
  rw [show w_B3b0c2_1_2 = .reuse ((GGResIShape.B3b0c2.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b0c2.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b0c2.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b0c2_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_B3b0c2_2_0) = true := by
  rw [show w_B3b0c2_2_0 = .reuse ((GGResIShape.B3b0c2.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b0c2.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b0c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b0c2.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b0c2_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_B3b0c2_2_1) = true := by
  rw [show w_B3b0c2_2_1 = .residual .B3b0c2 from rfl]
  exact ggResQTwoCellCheckK_imp (.residual .B3b0c2) (by decide +kernel)

theorem hcell_B3b0c2_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 0 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_B3b0c2_2_2) = true := by
  rw [show w_B3b0c2_2_2 = .reuse ((GGResIShape.B3b0c2.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b0c2.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b0c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b0c2.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_B3b0c2 : List (ℕ × ℕ × GGResQTwoCell 3) :=
  [(0, 0, w_B3b0c2_0_0), (0, 1, w_B3b0c2_0_1), (0, 2, w_B3b0c2_0_2), (1, 0, w_B3b0c2_1_0), (1, 1, w_B3b0c2_1_1), (1, 2, w_B3b0c2_1_2), (2, 0, w_B3b0c2_2_0), (2, 1, w_B3b0c2_2_1), (2, 2, w_B3b0c2_2_2)]

theorem hwits_B3b0c2 :
    GGResQTwoCellCheckAll (CartanMatrix.B 3) 0 2 (-1) (-1) wits_B3b0c2 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_0_0) (by rfl)]
      exact hcell_B3b0c2_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_0_1) (by rfl)]
      exact hcell_B3b0c2_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_0_2) (by rfl)]
      exact hcell_B3b0c2_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_1_0) (by rfl)]
      exact hcell_B3b0c2_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_1_1) (by rfl)]
      exact hcell_B3b0c2_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_1_2) (by rfl)]
      exact hcell_B3b0c2_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_2_0) (by rfl)]
      exact hcell_B3b0c2_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_2_1) (by rfl)]
      exact hcell_B3b0c2_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b0c2_2_2) (by rfl)]
      exact hcell_B3b0c2_2_2

@[expose] def w_B3b2c0_0_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0_0_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0_0_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0_1_0 : GGResQTwoCell 3 :=
  .commonKernel [1, 1, 2, 1]

@[expose] def w_B3b2c0_1_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0_1_2 : GGResQTwoCell 3 :=
  .residual .B3b2c0

@[expose] def w_B3b2c0_2_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0_2_1 : GGResQTwoCell 3 :=
  .commonKernel [0, 2, 2, 1]

@[expose] def w_B3b2c0_2_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_B3b2c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_B3b2c0_0_0) = true := by
  rw [show w_B3b2c0_0_0 = .reuse ((GGResIShape.B3b2c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_B3b2c0_0_1) = true := by
  rw [show w_B3b2c0_0_1 = .reuse ((GGResIShape.B3b2c0.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c0.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_B3b2c0_0_2) = true := by
  rw [show w_B3b2c0_0_2 = .reuse ((GGResIShape.B3b2c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_B3b2c0_1_0) = true := by
  rw [show w_B3b2c0_1_0 = .commonKernel [1, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 2, 1]) (by decide +kernel)

theorem hcell_B3b2c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_B3b2c0_1_1) = true := by
  rw [show w_B3b2c0_1_1 = .reuse ((GGResIShape.B3b2c0.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c0.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_B3b2c0_1_2) = true := by
  rw [show w_B3b2c0_1_2 = .residual .B3b2c0 from rfl]
  exact ggResQTwoCellCheckK_imp (.residual .B3b2c0) (by decide +kernel)

theorem hcell_B3b2c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_B3b2c0_2_0) = true := by
  rw [show w_B3b2c0_2_0 = .reuse ((GGResIShape.B3b2c0.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c0.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_B3b2c0_2_1) = true := by
  rw [show w_B3b2c0_2_1 = .commonKernel [0, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 2, 1]) (by decide +kernel)

theorem hcell_B3b2c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_B3b2c0_2_2) = true := by
  rw [show w_B3b2c0_2_2 = .reuse ((GGResIShape.B3b2c0.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c0.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_B3b2c0 : List (ℕ × ℕ × GGResQTwoCell 3) :=
  [(0, 0, w_B3b2c0_0_0), (0, 1, w_B3b2c0_0_1), (0, 2, w_B3b2c0_0_2), (1, 0, w_B3b2c0_1_0), (1, 1, w_B3b2c0_1_1), (1, 2, w_B3b2c0_1_2), (2, 0, w_B3b2c0_2_0), (2, 1, w_B3b2c0_2_1), (2, 2, w_B3b2c0_2_2)]

theorem hwits_B3b2c0 :
    GGResQTwoCellCheckAll (CartanMatrix.B 3) 2 0 (-1) (-1) wits_B3b2c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_0_0) (by rfl)]
      exact hcell_B3b2c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_0_1) (by rfl)]
      exact hcell_B3b2c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_0_2) (by rfl)]
      exact hcell_B3b2c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_1_0) (by rfl)]
      exact hcell_B3b2c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_1_1) (by rfl)]
      exact hcell_B3b2c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_1_2) (by rfl)]
      exact hcell_B3b2c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_2_0) (by rfl)]
      exact hcell_B3b2c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_2_1) (by rfl)]
      exact hcell_B3b2c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0_2_2) (by rfl)]
      exact hcell_B3b2c0_2_2

@[expose] def w_B3b2c0w12_0_0 : GGResQTwoCell 3 :=
  .commonKernel [2, 2, 1, 1]

@[expose] def w_B3b2c0w12_0_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w12_0_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w12_1_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w12_1_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w12_1_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w12_2_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w12_2_1 : GGResQTwoCell 3 :=
  .commonKernel [1, 0, 1, 1]

@[expose] def w_B3b2c0w12_2_2 : GGResQTwoCell 3 :=
  .residual .B3b2c0w12

theorem hcell_B3b2c0w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_B3b2c0w12_0_0) = true := by
  rw [show w_B3b2c0w12_0_0 = .commonKernel [2, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 2, 1, 1]) (by decide +kernel)

theorem hcell_B3b2c0w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_B3b2c0w12_0_1) = true := by
  rw [show w_B3b2c0w12_0_1 = .reuse ((GGResIShape.B3b2c0w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_B3b2c0w12_0_2) = true := by
  rw [show w_B3b2c0w12_0_2 = .reuse ((GGResIShape.B3b2c0w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_B3b2c0w12_1_0) = true := by
  rw [show w_B3b2c0w12_1_0 = .reuse ((GGResIShape.B3b2c0w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_B3b2c0w12_1_1) = true := by
  rw [show w_B3b2c0w12_1_1 = .reuse ((GGResIShape.B3b2c0w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_B3b2c0w12_1_2) = true := by
  rw [show w_B3b2c0w12_1_2 = .reuse ((GGResIShape.B3b2c0w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_B3b2c0w12_2_0) = true := by
  rw [show w_B3b2c0w12_2_0 = .reuse ((GGResIShape.B3b2c0w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_B3b2c0w12_2_1) = true := by
  rw [show w_B3b2c0w12_2_1 = .commonKernel [1, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 0, 1, 1]) (by decide +kernel)

theorem hcell_B3b2c0w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_B3b2c0w12_2_2) = true := by
  rw [show w_B3b2c0w12_2_2 = .residual .B3b2c0w12 from rfl]
  exact ggResQTwoCellCheckK_imp (.residual .B3b2c0w12) (by decide +kernel)

@[expose] def wits_B3b2c0w12 : List (ℕ × ℕ × GGResQTwoCell 3) :=
  [(0, 0, w_B3b2c0w12_0_0), (0, 1, w_B3b2c0w12_0_1), (0, 2, w_B3b2c0w12_0_2), (1, 0, w_B3b2c0w12_1_0), (1, 1, w_B3b2c0w12_1_1), (1, 2, w_B3b2c0w12_1_2), (2, 0, w_B3b2c0w12_2_0), (2, 1, w_B3b2c0w12_2_1), (2, 2, w_B3b2c0w12_2_2)]

theorem hwits_B3b2c0w12 :
    GGResQTwoCellCheckAll (CartanMatrix.B 3) 2 0 (-1) (-2) wits_B3b2c0w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_0_0) (by rfl)]
      exact hcell_B3b2c0w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_0_1) (by rfl)]
      exact hcell_B3b2c0w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_0_2) (by rfl)]
      exact hcell_B3b2c0w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_1_0) (by rfl)]
      exact hcell_B3b2c0w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_1_1) (by rfl)]
      exact hcell_B3b2c0w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_1_2) (by rfl)]
      exact hcell_B3b2c0w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_2_0) (by rfl)]
      exact hcell_B3b2c0w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_2_1) (by rfl)]
      exact hcell_B3b2c0w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w12_2_2) (by rfl)]
      exact hcell_B3b2c0w12_2_2

@[expose] def w_B3b2c0w21_0_0 : GGResQTwoCell 3 :=
  .commonKernel [1, 1, 2, 1]

@[expose] def w_B3b2c0w21_0_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w21_0_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w21_1_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w21_1_1 : GGResQTwoCell 3 :=
  .residual .B3b2c0w21

@[expose] def w_B3b2c0w21_1_2 : GGResQTwoCell 3 :=
  .commonKernel [2, 0, 2, 1]

@[expose] def w_B3b2c0w21_2_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w21_2_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c0w21_2_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_B3b2c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_B3b2c0w21_0_0) = true := by
  rw [show w_B3b2c0w21_0_0 = .commonKernel [1, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 2, 1]) (by decide +kernel)

theorem hcell_B3b2c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_B3b2c0w21_0_1) = true := by
  rw [show w_B3b2c0w21_0_1 = .reuse ((GGResIShape.B3b2c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_B3b2c0w21_0_2) = true := by
  rw [show w_B3b2c0w21_0_2 = .reuse ((GGResIShape.B3b2c0w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_B3b2c0w21_1_0) = true := by
  rw [show w_B3b2c0w21_1_0 = .reuse ((GGResIShape.B3b2c0w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_B3b2c0w21_1_1) = true := by
  rw [show w_B3b2c0w21_1_1 = .residual .B3b2c0w21 from rfl]
  exact ggResQTwoCellCheckK_imp (.residual .B3b2c0w21) (by decide +kernel)

theorem hcell_B3b2c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_B3b2c0w21_1_2) = true := by
  rw [show w_B3b2c0w21_1_2 = .commonKernel [2, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 2, 1]) (by decide +kernel)

theorem hcell_B3b2c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_B3b2c0w21_2_0) = true := by
  rw [show w_B3b2c0w21_2_0 = .reuse ((GGResIShape.B3b2c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_B3b2c0w21_2_1) = true := by
  rw [show w_B3b2c0w21_2_1 = .reuse ((GGResIShape.B3b2c0w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_B3b2c0w21_2_2) = true := by
  rw [show w_B3b2c0w21_2_2 = .reuse ((GGResIShape.B3b2c0w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c0w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_B3b2c0w21 : List (ℕ × ℕ × GGResQTwoCell 3) :=
  [(0, 0, w_B3b2c0w21_0_0), (0, 1, w_B3b2c0w21_0_1), (0, 2, w_B3b2c0w21_0_2), (1, 0, w_B3b2c0w21_1_0), (1, 1, w_B3b2c0w21_1_1), (1, 2, w_B3b2c0w21_1_2), (2, 0, w_B3b2c0w21_2_0), (2, 1, w_B3b2c0w21_2_1), (2, 2, w_B3b2c0w21_2_2)]

theorem hwits_B3b2c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.B 3) 2 0 (-2) (-1) wits_B3b2c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_0_0) (by rfl)]
      exact hcell_B3b2c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_0_1) (by rfl)]
      exact hcell_B3b2c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_0_2) (by rfl)]
      exact hcell_B3b2c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_1_0) (by rfl)]
      exact hcell_B3b2c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_1_1) (by rfl)]
      exact hcell_B3b2c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_1_2) (by rfl)]
      exact hcell_B3b2c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_2_0) (by rfl)]
      exact hcell_B3b2c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_2_1) (by rfl)]
      exact hcell_B3b2c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c0w21_2_2) (by rfl)]
      exact hcell_B3b2c0w21_2_2

@[expose] def w_B3b2c1_0_0 : GGResQTwoCell 3 :=
  .commonKernel [1, 2, 1, 1]

@[expose] def w_B3b2c1_0_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1_0_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1_1_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1_1_1 : GGResQTwoCell 3 :=
  .commonKernel [0, 0, 1, 1]

@[expose] def w_B3b2c1_1_2 : GGResQTwoCell 3 :=
  .residual .B3b2c1

@[expose] def w_B3b2c1_2_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1_2_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1_2_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_B3b2c1_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_B3b2c1_0_0) = true := by
  rw [show w_B3b2c1_0_0 = .commonKernel [1, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 1, 1]) (by decide +kernel)

theorem hcell_B3b2c1_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_B3b2c1_0_1) = true := by
  rw [show w_B3b2c1_0_1 = .reuse ((GGResIShape.B3b2c1.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c1.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_B3b2c1_0_2) = true := by
  rw [show w_B3b2c1_0_2 = .reuse ((GGResIShape.B3b2c1.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c1.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_B3b2c1_1_0) = true := by
  rw [show w_B3b2c1_1_0 = .reuse ((GGResIShape.B3b2c1.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c1.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_B3b2c1_1_1) = true := by
  rw [show w_B3b2c1_1_1 = .commonKernel [0, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 1, 1]) (by decide +kernel)

theorem hcell_B3b2c1_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_B3b2c1_1_2) = true := by
  rw [show w_B3b2c1_1_2 = .residual .B3b2c1 from rfl]
  exact ggResQTwoCellCheckK_imp (.residual .B3b2c1) (by decide +kernel)

theorem hcell_B3b2c1_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_B3b2c1_2_0) = true := by
  rw [show w_B3b2c1_2_0 = .reuse ((GGResIShape.B3b2c1.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c1.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_B3b2c1_2_1) = true := by
  rw [show w_B3b2c1_2_1 = .reuse ((GGResIShape.B3b2c1.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c1.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_B3b2c1_2_2) = true := by
  rw [show w_B3b2c1_2_2 = .reuse ((GGResIShape.B3b2c1.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c1.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_B3b2c1 : List (ℕ × ℕ × GGResQTwoCell 3) :=
  [(0, 0, w_B3b2c1_0_0), (0, 1, w_B3b2c1_0_1), (0, 2, w_B3b2c1_0_2), (1, 0, w_B3b2c1_1_0), (1, 1, w_B3b2c1_1_1), (1, 2, w_B3b2c1_1_2), (2, 0, w_B3b2c1_2_0), (2, 1, w_B3b2c1_2_1), (2, 2, w_B3b2c1_2_2)]

theorem hwits_B3b2c1 :
    GGResQTwoCellCheckAll (CartanMatrix.B 3) 2 1 (-1) (-1) wits_B3b2c1 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_0_0) (by rfl)]
      exact hcell_B3b2c1_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_0_1) (by rfl)]
      exact hcell_B3b2c1_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_0_2) (by rfl)]
      exact hcell_B3b2c1_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_1_0) (by rfl)]
      exact hcell_B3b2c1_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_1_1) (by rfl)]
      exact hcell_B3b2c1_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_1_2) (by rfl)]
      exact hcell_B3b2c1_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_2_0) (by rfl)]
      exact hcell_B3b2c1_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_2_1) (by rfl)]
      exact hcell_B3b2c1_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1_2_2) (by rfl)]
      exact hcell_B3b2c1_2_2

@[expose] def w_B3b2c1w12_0_0 : GGResQTwoCell 3 :=
  .residual .B3b2c1w12

@[expose] def w_B3b2c1w12_0_1 : GGResQTwoCell 3 :=
  .commonKernel [1, 2, 2, 1]

@[expose] def w_B3b2c1w12_0_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w12_1_0 : GGResQTwoCell 3 :=
  .commonKernel [2, 1, 2, 1]

@[expose] def w_B3b2c1w12_1_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w12_1_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w12_2_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w12_2_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w12_2_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w12.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_B3b2c1w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_B3b2c1w12_0_0) = true := by
  rw [show w_B3b2c1w12_0_0 = .residual .B3b2c1w12 from rfl]
  exact ggResQTwoCellCheckK_imp (.residual .B3b2c1w12) (by decide +kernel)

theorem hcell_B3b2c1w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_B3b2c1w12_0_1) = true := by
  rw [show w_B3b2c1w12_0_1 = .commonKernel [1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 2, 1]) (by decide +kernel)

theorem hcell_B3b2c1w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_B3b2c1w12_0_2) = true := by
  rw [show w_B3b2c1w12_0_2 = .reuse ((GGResIShape.B3b2c1w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c1w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_B3b2c1w12_1_0) = true := by
  rw [show w_B3b2c1w12_1_0 = .commonKernel [2, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 2, 1]) (by decide +kernel)

theorem hcell_B3b2c1w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_B3b2c1w12_1_1) = true := by
  rw [show w_B3b2c1w12_1_1 = .reuse ((GGResIShape.B3b2c1w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c1w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_B3b2c1w12_1_2) = true := by
  rw [show w_B3b2c1w12_1_2 = .reuse ((GGResIShape.B3b2c1w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c1w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_B3b2c1w12_2_0) = true := by
  rw [show w_B3b2c1w12_2_0 = .reuse ((GGResIShape.B3b2c1w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c1w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_B3b2c1w12_2_1) = true := by
  rw [show w_B3b2c1w12_2_1 = .reuse ((GGResIShape.B3b2c1w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c1w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_B3b2c1w12_2_2) = true := by
  rw [show w_B3b2c1w12_2_2 = .reuse ((GGResIShape.B3b2c1w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c1w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_B3b2c1w12 : List (ℕ × ℕ × GGResQTwoCell 3) :=
  [(0, 0, w_B3b2c1w12_0_0), (0, 1, w_B3b2c1w12_0_1), (0, 2, w_B3b2c1w12_0_2), (1, 0, w_B3b2c1w12_1_0), (1, 1, w_B3b2c1w12_1_1), (1, 2, w_B3b2c1w12_1_2), (2, 0, w_B3b2c1w12_2_0), (2, 1, w_B3b2c1w12_2_1), (2, 2, w_B3b2c1w12_2_2)]

theorem hwits_B3b2c1w12 :
    GGResQTwoCellCheckAll (CartanMatrix.B 3) 2 1 (-1) (-2) wits_B3b2c1w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_0_0) (by rfl)]
      exact hcell_B3b2c1w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_0_1) (by rfl)]
      exact hcell_B3b2c1w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_0_2) (by rfl)]
      exact hcell_B3b2c1w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_1_0) (by rfl)]
      exact hcell_B3b2c1w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_1_1) (by rfl)]
      exact hcell_B3b2c1w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_1_2) (by rfl)]
      exact hcell_B3b2c1w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_2_0) (by rfl)]
      exact hcell_B3b2c1w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_2_1) (by rfl)]
      exact hcell_B3b2c1w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w12_2_2) (by rfl)]
      exact hcell_B3b2c1w12_2_2

@[expose] def w_B3b2c1w21_0_0 : GGResQTwoCell 3 :=
  .residual .B3b2c1w21

@[expose] def w_B3b2c1w21_0_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w21_0_2 : GGResQTwoCell 3 :=
  .commonKernel [2, 1, 1, 1]

@[expose] def w_B3b2c1w21_1_0 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w21_1_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w21_1_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w21_2_0 : GGResQTwoCell 3 :=
  .commonKernel [1, 2, 1, 1]

@[expose] def w_B3b2c1w21_2_1 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_B3b2c1w21_2_2 : GGResQTwoCell 3 :=
  .reuse ((GGResIShape.B3b2c1w21.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_B3b2c1w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_B3b2c1w21_0_0) = true := by
  rw [show w_B3b2c1w21_0_0 = .residual .B3b2c1w21 from rfl]
  exact ggResQTwoCellCheckK_imp (.residual .B3b2c1w21) (by decide +kernel)

theorem hcell_B3b2c1w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_B3b2c1w21_0_1) = true := by
  rw [show w_B3b2c1w21_0_1 = .reuse ((GGResIShape.B3b2c1w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c1w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_B3b2c1w21_0_2) = true := by
  rw [show w_B3b2c1w21_0_2 = .commonKernel [2, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 1, 1]) (by decide +kernel)

theorem hcell_B3b2c1w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_B3b2c1w21_1_0) = true := by
  rw [show w_B3b2c1w21_1_0 = .reuse ((GGResIShape.B3b2c1w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B3b2c1w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_B3b2c1w21_1_1) = true := by
  rw [show w_B3b2c1w21_1_1 = .reuse ((GGResIShape.B3b2c1w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c1w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_B3b2c1w21_1_2) = true := by
  rw [show w_B3b2c1w21_1_2 = .reuse ((GGResIShape.B3b2c1w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c1w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_B3b2c1w21_2_0) = true := by
  rw [show w_B3b2c1w21_2_0 = .commonKernel [1, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 1, 1]) (by decide +kernel)

theorem hcell_B3b2c1w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_B3b2c1w21_2_1) = true := by
  rw [show w_B3b2c1w21_2_1 = .reuse ((GGResIShape.B3b2c1w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B3b2c1w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B3b2c1w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 3) 2 1 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_B3b2c1w21_2_2) = true := by
  rw [show w_B3b2c1w21_2_2 = .reuse ((GGResIShape.B3b2c1w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B3b2c1w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B3b2c1w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B3b2c1w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_B3b2c1w21 : List (ℕ × ℕ × GGResQTwoCell 3) :=
  [(0, 0, w_B3b2c1w21_0_0), (0, 1, w_B3b2c1w21_0_1), (0, 2, w_B3b2c1w21_0_2), (1, 0, w_B3b2c1w21_1_0), (1, 1, w_B3b2c1w21_1_1), (1, 2, w_B3b2c1w21_1_2), (2, 0, w_B3b2c1w21_2_0), (2, 1, w_B3b2c1w21_2_1), (2, 2, w_B3b2c1w21_2_2)]

theorem hwits_B3b2c1w21 :
    GGResQTwoCellCheckAll (CartanMatrix.B 3) 2 1 (-2) (-1) wits_B3b2c1w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_0_0) (by rfl)]
      exact hcell_B3b2c1w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_0_1) (by rfl)]
      exact hcell_B3b2c1w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_0_2) (by rfl)]
      exact hcell_B3b2c1w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_1_0) (by rfl)]
      exact hcell_B3b2c1w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_1_1) (by rfl)]
      exact hcell_B3b2c1w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_1_2) (by rfl)]
      exact hcell_B3b2c1w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_2_0) (by rfl)]
      exact hcell_B3b2c1w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_2_1) (by rfl)]
      exact hcell_B3b2c1w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B3b2c1w21_2_2) (by rfl)]
      exact hcell_B3b2c1w21_2_2

@[expose] def wits_B3_b0 (s : Fin 3 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 3) :=
  if s = (2, -1, -1) then wits_B3b0c2
  else []

theorem cell_B3_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.B 3) 0 (GGResIDisp.B3.shapes_B3_b0) (wits_B3_b0) := by
  intro s hs
  simp only [GGResIDisp.B3.shapes_B3_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · simp only [wits_B3_b0, if_pos rfl]
    exact hwits_B3b0c2
theorem hsideOK_B3_b0 :
    ∀ s ∈ GGResIDisp.B3.shapes_B3_b0, ∀ w ∈ wits_B3_b0 s,
      ggResQTwoCellSideOK (0 : Fin 3) w.2.2 := by
  have hall : (GGResIDisp.B3.shapes_B3_b0.all fun s => (wits_B3_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 3) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_B3_b0 :
    ∀ s ∈ GGResIDisp.B3.shapes_B3_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.B3.shapes_B3_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def wits_B3_b2 (s : Fin 3 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 3) :=
  if s = (0, -1, -1) then wits_B3b2c0
  else if s = (0, -1, -2) then wits_B3b2c0w12
  else if s = (0, -2, -1) then wits_B3b2c0w21
  else if s = (1, -1, -1) then wits_B3b2c1
  else if s = (1, -1, -2) then wits_B3b2c1w12
  else if s = (1, -2, -1) then wits_B3b2c1w21
  else []

theorem cell_B3_b2 :
    GGResQTwoShapeCoverage (CartanMatrix.B 3) 2 (GGResIDisp.B3.shapes_B3_b2) (wits_B3_b2) := by
  intro s hs
  simp only [GGResIDisp.B3.shapes_B3_b2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_B3_b2, if_pos rfl]
    exact hwits_B3b2c0
  · simp only [wits_B3_b2, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_B3b2c0w12
  · simp only [wits_B3_b2, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_B3b2c0w21
  · simp only [wits_B3_b2, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_B3b2c1
  · simp only [wits_B3_b2, if_neg (by decide : ¬ (((1, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((1, -1, -2)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_B3b2c1w12
  · simp only [wits_B3_b2, if_neg (by decide : ¬ (((1, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((1, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((1, -2, -1)) = ((1, -1, -2)))), if_pos rfl]
    exact hwits_B3b2c1w21
theorem hsideOK_B3_b2 :
    ∀ s ∈ GGResIDisp.B3.shapes_B3_b2, ∀ w ∈ wits_B3_b2 s,
      ggResQTwoCellSideOK (2 : Fin 3) w.2.2 := by
  have hall : (GGResIDisp.B3.shapes_B3_b2.all fun s => (wits_B3_b2 s).all fun w =>
      ggResQTwoCellSideOKB (2 : Fin 3) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_B3_b2 :
    ∀ s ∈ GGResIDisp.B3.shapes_B3_b2, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.B3.shapes_B3_b2.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataB3
