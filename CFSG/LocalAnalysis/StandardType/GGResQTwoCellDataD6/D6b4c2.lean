module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.Common

public section

namespace CFSG.StandardType.GGResQTwoCellDataD6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def w_D6b4c2_0_0 : GGResQTwoCell 6 :=
  .norm [0, 1, 2, 3, 4, 5] [1, 2, 0, 0, 0, 0, 1] Rq2_083533c7c9cbee7d [6, 2, 1, 0, 3, 2, 1, 4, 5, 3, 2, 6, 2, 3, 5, 4, 1, 2, 3, 0, 1, 2, 6] 1

@[expose] def w_D6b4c2_0_1 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b4c2.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D6b4c2_0_2 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b4c2.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D6b4c2_1_0 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b4c2.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D6b4c2_1_1 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b4c2.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D6b4c2_1_2 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b4c2.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D6b4c2_2_0 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b4c2.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D6b4c2_2_1 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.D6b4c2.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D6b4c2_2_2 : GGResQTwoCell 6 :=
  .norm [0, 1, 2, 3, 4, 5] [0, 0, 0, 2, 0, 1, 1] Rq2_083533c7c9cbee7d [6, 2, 1, 3, 2, 4, 6, 4, 2, 3, 1, 2, 6] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_D6b4c2_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 6) 4 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4, 5] Rq2_083533c7c9cbee7d [1, 2, 0, 0, 0, 0, 1] [6, 2, 1, 0, 3, 2, 1, 4, 5, 3, 2, 6, 2, 3, 5, 4, 1, 2, 3, 0, 1, 2, 6] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD6) (by decide +kernel)
    (by decide +kernel) (pkListD6 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D6b4c2_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 6) 4 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5] Rq2_083533c7c9cbee7d [0, 0, 0, 2, 0, 1, 1] [6, 2, 1, 3, 2, 4, 6, 4, 2, 3, 1, 2, 6] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD6) (by decide +kernel)
    (by decide +kernel) (pkListD6 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D6b4c2_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D6b4c2_0_0) = true := by
  rw [show w_D6b4c2_0_0 = .norm [0, 1, 2, 3, 4, 5] [1, 2, 0, 0, 0, 0, 1] Rq2_083533c7c9cbee7d [6, 2, 1, 0, 3, 2, 1, 4, 5, 3, 2, 6, 2, 3, 5, 4, 1, 2, 3, 0, 1, 2, 6] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5] [1, 2, 0, 0, 0, 0, 1] Rq2_083533c7c9cbee7d [6, 2, 1, 0, 3, 2, 1, 4, 5, 3, 2, 6, 2, 3, 5, 4, 1, 2, 3, 0, 1, 2, 6] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D6b4c2_0_0

theorem hcell_D6b4c2_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D6b4c2_0_1) = true := by
  rw [show w_D6b4c2_0_1 = .reuse ((GGResIShape.D6b4c2.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b4c2.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D6b4c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D6b4c2.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b4c2_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D6b4c2_0_2) = true := by
  rw [show w_D6b4c2_0_2 = .reuse ((GGResIShape.D6b4c2.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b4c2.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D6b4c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D6b4c2.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b4c2_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D6b4c2_1_0) = true := by
  rw [show w_D6b4c2_1_0 = .reuse ((GGResIShape.D6b4c2.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b4c2.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D6b4c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D6b4c2.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b4c2_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D6b4c2_1_1) = true := by
  rw [show w_D6b4c2_1_1 = .reuse ((GGResIShape.D6b4c2.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b4c2.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D6b4c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D6b4c2.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b4c2_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D6b4c2_1_2) = true := by
  rw [show w_D6b4c2_1_2 = .reuse ((GGResIShape.D6b4c2.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b4c2.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D6b4c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D6b4c2.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b4c2_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D6b4c2_2_0) = true := by
  rw [show w_D6b4c2_2_0 = .reuse ((GGResIShape.D6b4c2.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b4c2.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D6b4c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D6b4c2.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b4c2_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D6b4c2_2_1) = true := by
  rw [show w_D6b4c2_2_1 = .reuse ((GGResIShape.D6b4c2.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D6b4c2.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D6b4c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D6b4c2.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D6b4c2_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 6) 4 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D6b4c2_2_2) = true := by
  rw [show w_D6b4c2_2_2 = .norm [0, 1, 2, 3, 4, 5] [0, 0, 0, 2, 0, 1, 1] Rq2_083533c7c9cbee7d [6, 2, 1, 3, 2, 4, 6, 4, 2, 3, 1, 2, 6] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5] [0, 0, 0, 2, 0, 1, 1] Rq2_083533c7c9cbee7d [6, 2, 1, 3, 2, 4, 6, 4, 2, 3, 1, 2, 6] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D6b4c2_2_2

@[expose] def wits_D6b4c2 : List (ℕ × ℕ × GGResQTwoCell 6) :=
  [(0, 0, w_D6b4c2_0_0), (0, 1, w_D6b4c2_0_1), (0, 2, w_D6b4c2_0_2), (1, 0, w_D6b4c2_1_0), (1, 1, w_D6b4c2_1_1), (1, 2, w_D6b4c2_1_2), (2, 0, w_D6b4c2_2_0), (2, 1, w_D6b4c2_2_1), (2, 2, w_D6b4c2_2_2)]

theorem hwits_D6b4c2 :
    GGResQTwoCellCheckAll (CartanMatrix.D 6) 4 2 (-1) (-1) wits_D6b4c2 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_0_0) (by rfl)]
      exact hcell_D6b4c2_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_0_1) (by rfl)]
      exact hcell_D6b4c2_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_0_2) (by rfl)]
      exact hcell_D6b4c2_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_1_0) (by rfl)]
      exact hcell_D6b4c2_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_1_1) (by rfl)]
      exact hcell_D6b4c2_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_1_2) (by rfl)]
      exact hcell_D6b4c2_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_2_0) (by rfl)]
      exact hcell_D6b4c2_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_2_1) (by rfl)]
      exact hcell_D6b4c2_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D6b4c2_2_2) (by rfl)]
      exact hcell_D6b4c2_2_2

end CFSG.StandardType.GGResQTwoCellDataD6
