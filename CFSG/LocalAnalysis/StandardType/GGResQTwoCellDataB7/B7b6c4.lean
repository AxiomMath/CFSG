module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataB7.Common

public section

namespace CFSG.StandardType.GGResQTwoCellDataB7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def w_B7b6c4_0_0 : GGResQTwoCell 7 :=
  .commonKernel [1, 2, 0, 1, 2, 2, 1, 1]

@[expose] def w_B7b6c4_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.B7b6c4.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_B7b6c4_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.B7b6c4.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_B7b6c4_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.B7b6c4.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_B7b6c4_1_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.B7b6c4.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_B7b6c4_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 2, 0, 1] Rq2_0493c8fcbd77160b [7, 4, 3, 5, 4, 7, 6, 7, 4, 5, 3, 4, 7] 2

@[expose] def w_B7b6c4_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.B7b6c4.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_B7b6c4_2_1 : GGResQTwoCell 7 :=
  .commonKernel [0, 0, 0, 0, 0, 2, 2, 1]

@[expose] def w_B7b6c4_2_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.B7b6c4.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_B7b6c4_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.B 7) 6 4 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0493c8fcbd77160b [2, 1, 0, 2, 1, 2, 0, 1] [7, 4, 3, 5, 4, 7, 6, 7, 4, 5, 3, 4, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataB7) (by decide +kernel)
    (by decide +kernel) (pkListB7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_B7b6c4_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_B7b6c4_0_0) = true := by
  rw [show w_B7b6c4_0_0 = .commonKernel [1, 2, 0, 1, 2, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 1, 2, 2, 1, 1]) (by decide +kernel)

theorem hcell_B7b6c4_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_B7b6c4_0_1) = true := by
  rw [show w_B7b6c4_0_1 = .reuse ((GGResIShape.B7b6c4.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B7b6c4.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B7b6c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B7b6c4.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B7b6c4_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_B7b6c4_0_2) = true := by
  rw [show w_B7b6c4_0_2 = .reuse ((GGResIShape.B7b6c4.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B7b6c4.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B7b6c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B7b6c4.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B7b6c4_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_B7b6c4_1_0) = true := by
  rw [show w_B7b6c4_1_0 = .reuse ((GGResIShape.B7b6c4.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B7b6c4.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B7b6c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B7b6c4.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B7b6c4_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_B7b6c4_1_1) = true := by
  rw [show w_B7b6c4_1_1 = .reuse ((GGResIShape.B7b6c4.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B7b6c4.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B7b6c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B7b6c4.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B7b6c4_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_B7b6c4_1_2) = true := by
  rw [show w_B7b6c4_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 2, 0, 1] Rq2_0493c8fcbd77160b [7, 4, 3, 5, 4, 7, 6, 7, 4, 5, 3, 4, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 2, 0, 1] Rq2_0493c8fcbd77160b [7, 4, 3, 5, 4, 7, 6, 7, 4, 5, 3, 4, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_B7b6c4_1_2

theorem hcell_B7b6c4_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_B7b6c4_2_0) = true := by
  rw [show w_B7b6c4_2_0 = .reuse ((GGResIShape.B7b6c4.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B7b6c4.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B7b6c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B7b6c4.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B7b6c4_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_B7b6c4_2_1) = true := by
  rw [show w_B7b6c4_2_1 = .commonKernel [0, 0, 0, 0, 0, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 0, 0, 2, 2, 1]) (by decide +kernel)

theorem hcell_B7b6c4_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 7) 6 4 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_B7b6c4_2_2) = true := by
  rw [show w_B7b6c4_2_2 = .reuse ((GGResIShape.B7b6c4.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B7b6c4.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B7b6c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B7b6c4.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_B7b6c4 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_B7b6c4_0_0), (0, 1, w_B7b6c4_0_1), (0, 2, w_B7b6c4_0_2), (1, 0, w_B7b6c4_1_0), (1, 1, w_B7b6c4_1_1), (1, 2, w_B7b6c4_1_2), (2, 0, w_B7b6c4_2_0), (2, 1, w_B7b6c4_2_1), (2, 2, w_B7b6c4_2_2)]

theorem hwits_B7b6c4 :
    GGResQTwoCellCheckAll (CartanMatrix.B 7) 6 4 (-1) (-1) wits_B7b6c4 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_0_0) (by rfl)]
      exact hcell_B7b6c4_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_0_1) (by rfl)]
      exact hcell_B7b6c4_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_0_2) (by rfl)]
      exact hcell_B7b6c4_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_1_0) (by rfl)]
      exact hcell_B7b6c4_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_1_1) (by rfl)]
      exact hcell_B7b6c4_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_1_2) (by rfl)]
      exact hcell_B7b6c4_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_2_0) (by rfl)]
      exact hcell_B7b6c4_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_2_1) (by rfl)]
      exact hcell_B7b6c4_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B7b6c4_2_2) (by rfl)]
      exact hcell_B7b6c4_2_2

end CFSG.StandardType.GGResQTwoCellDataB7
