module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.F4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPackedFull

public section

namespace CFSG.StandardType.GGResQTwoCellDataF4

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_4ec1f516e31a292e : List (Fin 5 × List (Fin 5)) :=
[(0, []), (1, []), (2, []), (4, []), (0, [1]), (0, [4]), (1, [2]), (2, [1]), (0, [2, 1]), (0, [4, 1]), (2, [0, 1]), (0, [1, 2, 1]), (0, [4, 2, 1]), (2, [4, 0, 1]), (0, [4, 1, 2, 1]), (0, [0, 4, 1, 2, 1])]

abbrev Rq2_91bad764e64d8c73 : List (Fin 5 × List (Fin 5)) :=
[(1, []), (2, []), (3, []), (4, []), (1, [2]), (2, [1]), (2, [3]), (3, [4]), (1, [3, 2]), (2, [3, 1]), (2, [4, 3]), (1, [4, 3, 2]), (2, [2, 3, 1]), (2, [4, 3, 1]), (2, [4, 2, 3, 1]), (2, [3, 4, 2, 3, 1])]

@[expose] def w_F4b0c3_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 1, 0, 2, 1]

@[expose] def w_F4b0c3_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_F4b0c3_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_F4b0c3_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_F4b0c3_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_F4b0c3_1_2 : GGResQTwoCell 4 :=
  .commonKernel [1, 1, 2, 0, 1]

@[expose] def w_F4b0c3_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def pkTab_F4b0c3_2_1 : ℕ := 706608195725578

@[expose] def pkData_F4b0c3_2_1 : List (ℕ × ℕ × ℕ) :=
[(4, 4, 281543721361413),
  (16, 16, 281560909631489),
  (64, 64, 351981243731969),
  (256, 256, 563293567586561),
  (36, 20, 281586683613205),
  (20, 24, 281569482809369),
  (80, 80, 369470400974849),
  (320, 320, 141287596495169),
  (164, 84, 466351860748373),
  (84, 88, 378270763884633),
  (336, 336, 175991251358033),
  (676, 340, 655377666412545),
  (100, 104, 395893077446761),
  (340, 344, 180389004616357),
  (356, 360, 163183696286357),
  (420, 424, 282183663096405)]

@[expose] def w_F4b0c3_2_1 : GGResQTwoCell 4 :=
  .norm [1, 2, 3, 4] [2, 0, 2, 1, 0] Rq2_91bad764e64d8c73 [0, 1, 2, 1, 4, 0, 4, 1, 2, 1, 0] 1

@[expose] def w_F4b0c3_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b0c3.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_F4b0c3_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.F₄) 0 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [1, 2, 3, 4] Rq2_91bad764e64d8c73 [2, 0, 2, 1, 0] [0, 1, 2, 1, 4, 0, 4, 1, 2, 1, 0] 1 := by
  exact GGResQTwoPackedFull.GGResQTwoNormOKK_of_pkF (D := pkData_F4b0c3_2_1) (by decide +kernel)
    (by decide +kernel)
    (GGResQTwoPackedFull.pkListF_std (tab := pkTab_F4b0c3_2_1) (by decide +kernel)
      (by decide +kernel))
    (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_F4b0c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_F4b0c3_0_0) = true := by
  rw [show w_F4b0c3_0_0 = .commonKernel [2, 1, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 1]) (by decide +kernel)

theorem hcell_F4b0c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_F4b0c3_0_1) = true := by
  rw [show w_F4b0c3_0_1 = .reuse ((GGResIShape.F4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b0c3.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.F4b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.F4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b0c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_F4b0c3_0_2) = true := by
  rw [show w_F4b0c3_0_2 = .reuse ((GGResIShape.F4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b0c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.F4b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.F4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b0c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_F4b0c3_1_0) = true := by
  rw [show w_F4b0c3_1_0 = .reuse ((GGResIShape.F4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b0c3.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.F4b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.F4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b0c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_F4b0c3_1_1) = true := by
  rw [show w_F4b0c3_1_1 = .reuse ((GGResIShape.F4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b0c3.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.F4b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.F4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b0c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_F4b0c3_1_2) = true := by
  rw [show w_F4b0c3_1_2 = .commonKernel [1, 1, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 2, 0, 1]) (by decide +kernel)

theorem hcell_F4b0c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_F4b0c3_2_0) = true := by
  rw [show w_F4b0c3_2_0 = .reuse ((GGResIShape.F4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b0c3.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.F4b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.F4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b0c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_F4b0c3_2_1) = true := by
  rw [show w_F4b0c3_2_1 = .norm [1, 2, 3, 4] [2, 0, 2, 1, 0] Rq2_91bad764e64d8c73 [0, 1, 2, 1, 4, 0, 4, 1, 2, 1, 0] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [1, 2, 3, 4] [2, 0, 2, 1, 0] Rq2_91bad764e64d8c73 [0, 1, 2, 1, 4, 0, 4, 1, 2, 1, 0] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_F4b0c3_2_1

theorem hcell_F4b0c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 0 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_F4b0c3_2_2) = true := by
  rw [show w_F4b0c3_2_2 = .reuse ((GGResIShape.F4b0c3.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b0c3.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.F4b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.F4b0c3.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_F4b0c3 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_F4b0c3_0_0), (0, 1, w_F4b0c3_0_1), (0, 2, w_F4b0c3_0_2), (1, 0, w_F4b0c3_1_0), (1, 1, w_F4b0c3_1_1), (1, 2, w_F4b0c3_1_2), (2, 0, w_F4b0c3_2_0), (2, 1, w_F4b0c3_2_1), (2, 2, w_F4b0c3_2_2)]

theorem hwits_F4b0c3 :
    GGResQTwoCellCheckAll (CartanMatrix.F₄) 0 3 (-1) (-1) wits_F4b0c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_0_0) (by rfl)]
      exact hcell_F4b0c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_0_1) (by rfl)]
      exact hcell_F4b0c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_0_2) (by rfl)]
      exact hcell_F4b0c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_1_0) (by rfl)]
      exact hcell_F4b0c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_1_1) (by rfl)]
      exact hcell_F4b0c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_1_2) (by rfl)]
      exact hcell_F4b0c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_2_0) (by rfl)]
      exact hcell_F4b0c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_2_1) (by rfl)]
      exact hcell_F4b0c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_F4b0c3_2_2) (by rfl)]
      exact hcell_F4b0c3_2_2

@[expose] def w_F4b3c0_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 0, 2, 1, 1]

@[expose] def w_F4b3c0_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b3c0.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_F4b3c0_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_F4b3c0_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b3c0.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_F4b3c0_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def pkTab_F4b3c0_1_2 : ℕ := 636239451548170

@[expose] def pkData_F4b3c0_1_2 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 282643224597506),
  (4, 4, 281543721361413),
  (16, 16, 281560909631489),
  (256, 256, 563568445493505),
  (5, 5, 287041281591304),
  (257, 257, 2819663074816),
  (36, 20, 281586683613205),
  (20, 24, 281569482809369),
  (37, 21, 304678576350248),
  (261, 261, 11624893646849),
  (21, 26, 310158932578342),
  (41, 25, 309072305891329),
  (293, 277, 46545941849089),
  (277, 538, 603700619907073),
  (297, 281, 42151900129562),
  (298, 282, 281846508163622)]

@[expose] def w_F4b3c0_1_2 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 4] [1, 2, 0, 1, 0] Rq2_4ec1f516e31a292e [3, 2, 1, 2, 4, 3, 4, 2, 1, 2, 3] 2

@[expose] def w_F4b3c0_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b3c0.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_F4b3c0_2_1 : GGResQTwoCell 4 :=
  .commonKernel [0, 2, 2, 2, 1]

@[expose] def w_F4b3c0_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.F4b3c0.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_F4b3c0_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.F₄) 3 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 4] Rq2_4ec1f516e31a292e [1, 2, 0, 1, 0] [3, 2, 1, 2, 4, 3, 4, 2, 1, 2, 3] 2 := by
  exact GGResQTwoPackedFull.GGResQTwoNormOKK_of_pkF (D := pkData_F4b3c0_1_2) (by decide +kernel)
    (by decide +kernel)
    (GGResQTwoPackedFull.pkListF_std (tab := pkTab_F4b3c0_1_2) (by decide +kernel)
      (by decide +kernel))
    (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_F4b3c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_F4b3c0_0_0) = true := by
  rw [show w_F4b3c0_0_0 = .commonKernel [2, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 2, 1, 1]) (by decide +kernel)

theorem hcell_F4b3c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_F4b3c0_0_1) = true := by
  rw [show w_F4b3c0_0_1 = .reuse ((GGResIShape.F4b3c0.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b3c0.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.F4b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.F4b3c0.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b3c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_F4b3c0_0_2) = true := by
  rw [show w_F4b3c0_0_2 = .reuse ((GGResIShape.F4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b3c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.F4b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.F4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b3c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_F4b3c0_1_0) = true := by
  rw [show w_F4b3c0_1_0 = .reuse ((GGResIShape.F4b3c0.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b3c0.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.F4b3c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.F4b3c0.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b3c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_F4b3c0_1_1) = true := by
  rw [show w_F4b3c0_1_1 = .reuse ((GGResIShape.F4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b3c0.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.F4b3c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.F4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b3c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_F4b3c0_1_2) = true := by
  rw [show w_F4b3c0_1_2 = .norm [0, 1, 2, 4] [1, 2, 0, 1, 0] Rq2_4ec1f516e31a292e [3, 2, 1, 2, 4, 3, 4, 2, 1, 2, 3] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 4] [1, 2, 0, 1, 0] Rq2_4ec1f516e31a292e [3, 2, 1, 2, 4, 3, 4, 2, 1, 2, 3] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_F4b3c0_1_2

theorem hcell_F4b3c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_F4b3c0_2_0) = true := by
  rw [show w_F4b3c0_2_0 = .reuse ((GGResIShape.F4b3c0.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b3c0.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.F4b3c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.F4b3c0.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_F4b3c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_F4b3c0_2_1) = true := by
  rw [show w_F4b3c0_2_1 = .commonKernel [0, 2, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 2, 2, 1]) (by decide +kernel)

theorem hcell_F4b3c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.F₄) 3 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_F4b3c0_2_2) = true := by
  rw [show w_F4b3c0_2_2 = .reuse ((GGResIShape.F4b3c0.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.F4b3c0.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.F4b3c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.F4b3c0.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_F4b3c0 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_F4b3c0_0_0), (0, 1, w_F4b3c0_0_1), (0, 2, w_F4b3c0_0_2), (1, 0, w_F4b3c0_1_0), (1, 1, w_F4b3c0_1_1), (1, 2, w_F4b3c0_1_2), (2, 0, w_F4b3c0_2_0), (2, 1, w_F4b3c0_2_1), (2, 2, w_F4b3c0_2_2)]

theorem hwits_F4b3c0 :
    GGResQTwoCellCheckAll (CartanMatrix.F₄) 3 0 (-1) (-1) wits_F4b3c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_0_0) (by rfl)]
      exact hcell_F4b3c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_0_1) (by rfl)]
      exact hcell_F4b3c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_0_2) (by rfl)]
      exact hcell_F4b3c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_1_0) (by rfl)]
      exact hcell_F4b3c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_1_1) (by rfl)]
      exact hcell_F4b3c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_1_2) (by rfl)]
      exact hcell_F4b3c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_2_0) (by rfl)]
      exact hcell_F4b3c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_2_1) (by rfl)]
      exact hcell_F4b3c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_F4b3c0_2_2) (by rfl)]
      exact hcell_F4b3c0_2_2

@[expose] def wits_F4_b0 (s : Fin 4 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 4) :=
  if s = (3, -1, -1) then wits_F4b0c3
  else []

theorem cell_F4_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.F₄) 0 (GGResIDisp.F4.shapes_F4_b0) (wits_F4_b0) := by
  intro s hs
  simp only [GGResIDisp.F4.shapes_F4_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · simp only [wits_F4_b0, if_pos rfl]
    exact hwits_F4b0c3
theorem hsideOK_F4_b0 :
    ∀ s ∈ GGResIDisp.F4.shapes_F4_b0, ∀ w ∈ wits_F4_b0 s,
      ggResQTwoCellSideOK (0 : Fin 4) w.2.2 := by
  have hall : (GGResIDisp.F4.shapes_F4_b0.all fun s => (wits_F4_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 4) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_F4_b0 :
    ∀ s ∈ GGResIDisp.F4.shapes_F4_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.F4.shapes_F4_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def wits_F4_b3 (s : Fin 4 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 4) :=
  if s = (0, -1, -1) then wits_F4b3c0
  else []

theorem cell_F4_b3 :
    GGResQTwoShapeCoverage (CartanMatrix.F₄) 3 (GGResIDisp.F4.shapes_F4_b3) (wits_F4_b3) := by
  intro s hs
  simp only [GGResIDisp.F4.shapes_F4_b3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · simp only [wits_F4_b3, if_pos rfl]
    exact hwits_F4b3c0
theorem hsideOK_F4_b3 :
    ∀ s ∈ GGResIDisp.F4.shapes_F4_b3, ∀ w ∈ wits_F4_b3 s,
      ggResQTwoCellSideOK (3 : Fin 4) w.2.2 := by
  have hall : (GGResIDisp.F4.shapes_F4_b3.all fun s => (wits_F4_b3 s).all fun w =>
      ggResQTwoCellSideOKB (3 : Fin 4) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_F4_b3 :
    ∀ s ∈ GGResIDisp.F4.shapes_F4_b3, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.F4.shapes_F4_b3.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataF4
