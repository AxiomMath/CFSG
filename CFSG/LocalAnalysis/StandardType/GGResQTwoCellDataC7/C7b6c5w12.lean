module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.Common

public section

namespace CFSG.StandardType.GGResQTwoCellDataC7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def w_C7b6c5w12_0_0 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 0, 0, 1] Rq2_0493c8fcbd77160b [7, 5, 4, 3, 6, 5, 4, 6, 5, 7, 5, 6, 4, 5, 6, 3, 4, 5, 7] 2

@[expose] def w_C7b6c5w12_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.C7b6c5w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C7b6c5w12_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.C7b6c5w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C7b6c5w12_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.C7b6c5w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C7b6c5w12_1_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.C7b6c5w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C7b6c5w12_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.C7b6c5w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C7b6c5w12_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.C7b6c5w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C7b6c5w12_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.C7b6c5w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C7b6c5w12_2_2 : GGResQTwoCell 7 :=
  .commonKernel [1, 2, 0, 1, 2, 0, 2, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_C7b6c5w12_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 7) 6 5 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0493c8fcbd77160b [2, 1, 0, 2, 1, 0, 0, 1] [7, 5, 4, 3, 6, 5, 4, 6, 5, 7, 5, 6, 4, 5, 6, 3, 4, 5, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC7) (by decide +kernel)
    (by decide +kernel) (pkListC7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C7b6c5w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_C7b6c5w12_0_0) = true := by
  rw [show w_C7b6c5w12_0_0 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 0, 0, 1] Rq2_0493c8fcbd77160b [7, 5, 4, 3, 6, 5, 4, 6, 5, 7, 5, 6, 4, 5, 6, 3, 4, 5, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 0, 0, 1] Rq2_0493c8fcbd77160b [7, 5, 4, 3, 6, 5, 4, 6, 5, 7, 5, 6, 4, 5, 6, 3, 4, 5, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C7b6c5w12_0_0

theorem hcell_C7b6c5w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_C7b6c5w12_0_1) = true := by
  rw [show w_C7b6c5w12_0_1 = .reuse ((GGResIShape.C7b6c5w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C7b6c5w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C7b6c5w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C7b6c5w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C7b6c5w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_C7b6c5w12_0_2) = true := by
  rw [show w_C7b6c5w12_0_2 = .reuse ((GGResIShape.C7b6c5w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C7b6c5w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C7b6c5w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C7b6c5w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C7b6c5w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_C7b6c5w12_1_0) = true := by
  rw [show w_C7b6c5w12_1_0 = .reuse ((GGResIShape.C7b6c5w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C7b6c5w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C7b6c5w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C7b6c5w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C7b6c5w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_C7b6c5w12_1_1) = true := by
  rw [show w_C7b6c5w12_1_1 = .reuse ((GGResIShape.C7b6c5w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C7b6c5w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C7b6c5w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C7b6c5w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C7b6c5w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_C7b6c5w12_1_2) = true := by
  rw [show w_C7b6c5w12_1_2 = .reuse ((GGResIShape.C7b6c5w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C7b6c5w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C7b6c5w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C7b6c5w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C7b6c5w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_C7b6c5w12_2_0) = true := by
  rw [show w_C7b6c5w12_2_0 = .reuse ((GGResIShape.C7b6c5w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C7b6c5w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C7b6c5w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C7b6c5w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C7b6c5w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_C7b6c5w12_2_1) = true := by
  rw [show w_C7b6c5w12_2_1 = .reuse ((GGResIShape.C7b6c5w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C7b6c5w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C7b6c5w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C7b6c5w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C7b6c5w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 7) 6 5 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_C7b6c5w12_2_2) = true := by
  rw [show w_C7b6c5w12_2_2 = .commonKernel [1, 2, 0, 1, 2, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 1, 2, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_C7b6c5w12 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_C7b6c5w12_0_0), (0, 1, w_C7b6c5w12_0_1), (0, 2, w_C7b6c5w12_0_2), (1, 0, w_C7b6c5w12_1_0), (1, 1, w_C7b6c5w12_1_1), (1, 2, w_C7b6c5w12_1_2), (2, 0, w_C7b6c5w12_2_0), (2, 1, w_C7b6c5w12_2_1), (2, 2, w_C7b6c5w12_2_2)]

theorem hwits_C7b6c5w12 :
    GGResQTwoCellCheckAll (CartanMatrix.C 7) 6 5 (-1) (-2) wits_C7b6c5w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_0_0) (by rfl)]
      exact hcell_C7b6c5w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_0_1) (by rfl)]
      exact hcell_C7b6c5w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_0_2) (by rfl)]
      exact hcell_C7b6c5w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_1_0) (by rfl)]
      exact hcell_C7b6c5w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_1_1) (by rfl)]
      exact hcell_C7b6c5w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_1_2) (by rfl)]
      exact hcell_C7b6c5w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_2_0) (by rfl)]
      exact hcell_C7b6c5w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_2_1) (by rfl)]
      exact hcell_C7b6c5w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C7b6c5w12_2_2) (by rfl)]
      exact hcell_C7b6c5w12_2_2

end CFSG.StandardType.GGResQTwoCellDataC7
