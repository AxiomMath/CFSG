module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData

public section

namespace CFSG.StandardType.GGResQTwoCellDataD6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def w_D6b5c0_0_0 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b5c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D6b5c0_0_1 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b5c0.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D6b5c0_0_2 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b5c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D6b5c0_1_0 : GGResQTwoCell 6 :=
  .commonKernel [1, 1, 1, 1, 2, 2, 1]

@[expose] def w_D6b5c0_1_1 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b5c0.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D6b5c0_1_2 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b5c0.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D6b5c0_2_0 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b5c0.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D6b5c0_2_1 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b5c0.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D6b5c0_2_2 : GGResQTwoCell 6 :=
  .commonKernel [0, 2, 1, 0, 0, 2, 1]

theorem hcell_D6b5c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D6b5c0_0_0) = true := by
  rw [show w_D6b5c0_0_0 = .reuse ((GGResIShape.D6b5c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b5c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D6b5c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D6b5c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b5c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D6b5c0_0_1) = true := by
  rw [show w_D6b5c0_0_1 = .reuse ((GGResIShape.D6b5c0.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b5c0.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D6b5c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D6b5c0.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b5c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D6b5c0_0_2) = true := by
  rw [show w_D6b5c0_0_2 = .reuse ((GGResIShape.D6b5c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b5c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D6b5c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D6b5c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b5c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D6b5c0_1_0) = true := by
  rw [show w_D6b5c0_1_0 = .commonKernel [1, 1, 1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D6b5c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D6b5c0_1_1) = true := by
  rw [show w_D6b5c0_1_1 = .reuse ((GGResIShape.D6b5c0.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b5c0.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D6b5c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D6b5c0.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b5c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D6b5c0_1_2) = true := by
  rw [show w_D6b5c0_1_2 = .reuse ((GGResIShape.D6b5c0.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b5c0.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D6b5c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D6b5c0.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b5c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D6b5c0_2_0) = true := by
  rw [show w_D6b5c0_2_0 = .reuse ((GGResIShape.D6b5c0.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b5c0.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D6b5c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D6b5c0.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b5c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D6b5c0_2_1) = true := by
  rw [show w_D6b5c0_2_1 = .reuse ((GGResIShape.D6b5c0.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b5c0.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D6b5c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D6b5c0.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b5c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 5 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D6b5c0_2_2) = true := by
  rw [show w_D6b5c0_2_2 = .commonKernel [0, 2, 1, 0, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 1, 0, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_D6b5c0 : List (ℕ × ℕ × GGResQTwoCell 6) :=
  [(0, 0, w_D6b5c0_0_0), (0, 1, w_D6b5c0_0_1), (0, 2, w_D6b5c0_0_2), (1, 0, w_D6b5c0_1_0), (1, 1, w_D6b5c0_1_1), (1, 2, w_D6b5c0_1_2), (2, 0, w_D6b5c0_2_0), (2, 1, w_D6b5c0_2_1), (2, 2, w_D6b5c0_2_2)]

theorem hwits_D6b5c0 :
    GGResQTwoCellCheckAll (CartanMatrix.D 6) 5 0 (-1) (-1) wits_D6b5c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_0_0) (by rfl)]
      exact hcell_D6b5c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_0_1) (by rfl)]
      exact hcell_D6b5c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_0_2) (by rfl)]
      exact hcell_D6b5c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_1_0) (by rfl)]
      exact hcell_D6b5c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_1_1) (by rfl)]
      exact hcell_D6b5c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_1_2) (by rfl)]
      exact hcell_D6b5c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_2_0) (by rfl)]
      exact hcell_D6b5c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_2_1) (by rfl)]
      exact hcell_D6b5c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D6b5c0_2_2) (by rfl)]
      exact hcell_D6b5c0_2_2

end CFSG.StandardType.GGResQTwoCellDataD6
