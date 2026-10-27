module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataB6.Common

public section

namespace CFSG.StandardType.GGResQTwoCellDataB6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def w_B6b5c0w21_0_0 : GGResQTwoCell 6 :=
  .commonKernel [1, 1, 1, 1, 1, 2, 1]

@[expose] def w_B6b5c0w21_0_1 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.B6b5c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_B6b5c0w21_0_2 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.B6b5c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_B6b5c0w21_1_0 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.B6b5c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_B6b5c0w21_1_1 : GGResQTwoCell 6 :=
  .norm [0, 1, 2, 3, 4, 5] [0, 2, 1, 0, 2, 2, 1] Rq2_03f192978eefee08 [6, 0, 5, 4, 5, 6, 5, 4, 5, 0, 6] 1

@[expose] def w_B6b5c0w21_1_2 : GGResQTwoCell 6 :=
  .commonKernel [2, 0, 1, 2, 0, 2, 1]

@[expose] def w_B6b5c0w21_2_0 : GGResQTwoCell 6 :=
  .reuse ((GGResIShape.B6b5c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_B6b5c0w21_2_1 : GGResQTwoCell 6 :=
  .commonKernel [0, 2, 1, 0, 2, 2, 1]

@[expose] def w_B6b5c0w21_2_2 : GGResQTwoCell 6 :=
  .norm [0, 1, 2, 3, 4, 5] [2, 0, 1, 2, 0, 2, 1] Rq2_03f192978eefee08 [6, 0, 5, 4, 5, 6, 5, 4, 5, 0, 6] 1

open scoped CFSG.Decide.Bounded in
theorem hnorm_B6b5c0w21_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.B 6) 5 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5] Rq2_03f192978eefee08 [0, 2, 1, 0, 2, 2, 1] [6, 0, 5, 4, 5, 6, 5, 4, 5, 0, 6] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataB6) (by decide +kernel)
    (by decide +kernel) (pkListB6 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_B6b5c0w21_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.B 6) 5 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5] Rq2_03f192978eefee08 [2, 0, 1, 2, 0, 2, 1] [6, 0, 5, 4, 5, 6, 5, 4, 5, 0, 6] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataB6) (by decide +kernel)
    (by decide +kernel) (pkListB6 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_B6b5c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_B6b5c0w21_0_0) = true := by
  rw [show w_B6b5c0w21_0_0 = .commonKernel [1, 1, 1, 1, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 1, 2, 1]) (by decide +kernel)

theorem hcell_B6b5c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_B6b5c0w21_0_1) = true := by
  rw [show w_B6b5c0w21_0_1 = .reuse ((GGResIShape.B6b5c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B6b5c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.B6b5c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.B6b5c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B6b5c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_B6b5c0w21_0_2) = true := by
  rw [show w_B6b5c0w21_0_2 = .reuse ((GGResIShape.B6b5c0w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B6b5c0w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.B6b5c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.B6b5c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B6b5c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_B6b5c0w21_1_0) = true := by
  rw [show w_B6b5c0w21_1_0 = .reuse ((GGResIShape.B6b5c0w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B6b5c0w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B6b5c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B6b5c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B6b5c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_B6b5c0w21_1_1) = true := by
  rw [show w_B6b5c0w21_1_1 = .norm [0, 1, 2, 3, 4, 5] [0, 2, 1, 0, 2, 2, 1] Rq2_03f192978eefee08 [6, 0, 5, 4, 5, 6, 5, 4, 5, 0, 6] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5] [0, 2, 1, 0, 2, 2, 1] Rq2_03f192978eefee08 [6, 0, 5, 4, 5, 6, 5, 4, 5, 0, 6] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_B6b5c0w21_1_1

theorem hcell_B6b5c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_B6b5c0w21_1_2) = true := by
  rw [show w_B6b5c0w21_1_2 = .commonKernel [2, 0, 1, 2, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 0, 2, 1]) (by decide +kernel)

theorem hcell_B6b5c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_B6b5c0w21_2_0) = true := by
  rw [show w_B6b5c0w21_2_0 = .reuse ((GGResIShape.B6b5c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.B6b5c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.B6b5c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.B6b5c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_B6b5c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_B6b5c0w21_2_1) = true := by
  rw [show w_B6b5c0w21_2_1 = .commonKernel [0, 2, 1, 0, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 1, 0, 2, 2, 1]) (by decide +kernel)

theorem hcell_B6b5c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.B 6) 5 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_B6b5c0w21_2_2) = true := by
  rw [show w_B6b5c0w21_2_2 = .norm [0, 1, 2, 3, 4, 5] [2, 0, 1, 2, 0, 2, 1] Rq2_03f192978eefee08 [6, 0, 5, 4, 5, 6, 5, 4, 5, 0, 6] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5] [2, 0, 1, 2, 0, 2, 1] Rq2_03f192978eefee08 [6, 0, 5, 4, 5, 6, 5, 4, 5, 0, 6] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_B6b5c0w21_2_2

@[expose] def wits_B6b5c0w21 : List (ℕ × ℕ × GGResQTwoCell 6) :=
  [(0, 0, w_B6b5c0w21_0_0), (0, 1, w_B6b5c0w21_0_1), (0, 2, w_B6b5c0w21_0_2), (1, 0, w_B6b5c0w21_1_0), (1, 1, w_B6b5c0w21_1_1), (1, 2, w_B6b5c0w21_1_2), (2, 0, w_B6b5c0w21_2_0), (2, 1, w_B6b5c0w21_2_1), (2, 2, w_B6b5c0w21_2_2)]

theorem hwits_B6b5c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.B 6) 5 0 (-2) (-1) wits_B6b5c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_0_0) (by rfl)]
      exact hcell_B6b5c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_0_1) (by rfl)]
      exact hcell_B6b5c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_0_2) (by rfl)]
      exact hcell_B6b5c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_1_0) (by rfl)]
      exact hcell_B6b5c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_1_1) (by rfl)]
      exact hcell_B6b5c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_1_2) (by rfl)]
      exact hcell_B6b5c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_2_0) (by rfl)]
      exact hcell_B6b5c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_2_1) (by rfl)]
      exact hcell_B6b5c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_B6b5c0w21_2_2) (by rfl)]
      exact hcell_B6b5c0w21_2_2

end CFSG.StandardType.GGResQTwoCellDataB6
