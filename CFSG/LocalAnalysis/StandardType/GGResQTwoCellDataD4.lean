module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPackedFull

public section

namespace CFSG.StandardType.GGResQTwoCellDataD4

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_3de60cfe5fc0fe41 : List (Fin 5 × List (Fin 5)) :=
[(0, []), (1, []), (2, []), (4, []), (0, [1]), (1, [2]), (2, [4]), (0, [2, 1]), (1, [4, 2]), (0, [4, 2, 1])]

abbrev Rq2_4ec79ddb38e2ca04 : List (Fin 5 × List (Fin 5)) :=
[(1, []), (2, []), (3, []), (4, []), (1, [2]), (1, [3]), (2, [4]), (1, [3, 2]), (1, [4, 2]), (1, [4, 3, 2])]

abbrev Rq2_5c2a94249d050724 : List (Fin 5 × List (Fin 5)) :=
[(0, []), (1, []), (2, []), (4, []), (0, [1]), (0, [4]), (1, [2]), (0, [2, 1]), (0, [4, 1]), (0, [4, 2, 1])]

abbrev Rq2_6585cb8f7470540e : List (Fin 5 × List (Fin 5)) :=
[(1, []), (2, []), (3, []), (4, []), (1, [2]), (1, [3]), (3, [4]), (1, [3, 2]), (1, [4, 3]), (1, [4, 3, 2])]

abbrev Rq2_73c3810ef43f8b4d : List (Fin 5 × List (Fin 5)) :=
[(0, []), (1, []), (3, []), (4, []), (0, [1]), (0, [4]), (1, [3]), (0, [3, 1]), (0, [4, 1]), (0, [4, 3, 1])]

abbrev Rq2_c4bef338e341afc5 : List (Fin 5 × List (Fin 5)) :=
[(0, []), (1, []), (3, []), (4, []), (0, [1]), (1, [3]), (3, [4]), (0, [3, 1]), (1, [4, 3]), (0, [4, 3, 1])]

@[expose] def w_D4b0c2_0_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def pkTab_D4b0c2_2_2 : ℕ := 600479956642314

@[expose] def pkData_D4b0c2_2_2 : List (ℕ × ℕ × ℕ) :=
[(4, 4, 281548012134405),
  (16, 16, 299135915806721),
  (64, 64, 281612432510977),
  (256, 256, 563018958115073),
  (20, 20, 303555412000789),
  (68, 68, 281483654856773),
  (272, 272, 35253628719377),
  (84, 84, 373877045727317),
  (276, 276, 44345554666025),
  (340, 340, 185310675735209)]

@[expose] def w_D4b0c2_2_2 : GGResQTwoCell 4 :=
  .norm [1, 2, 3, 4] [2, 2, 1, 1, 0] Rq2_4ec79ddb38e2ca04 [0, 1, 2, 3, 1, 0, 4, 0, 1, 3, 2, 1, 0] 3

open scoped CFSG.Decide.Bounded in
theorem hnorm_D4b0c2_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 4) 0 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [1, 2, 3, 4] Rq2_4ec79ddb38e2ca04 [2, 2, 1, 1, 0] [0, 1, 2, 3, 1, 0, 4, 0, 1, 3, 2, 1, 0] 3 := by
  exact GGResQTwoPackedFull.GGResQTwoNormOKK_of_pkF (D := pkData_D4b0c2_2_2) (by decide +kernel)
    (by decide +kernel)
    (GGResQTwoPackedFull.pkListF_std (tab := pkTab_D4b0c2_2_2) (by decide +kernel)
      (by decide +kernel))
    (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D4b0c2_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b0c2_0_0) = true := by
  rw [show w_D4b0c2_0_0 = .reuse ((GGResIShape.D4b0c2.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c2.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b0c2_0_1) = true := by
  rw [show w_D4b0c2_0_1 = .reuse ((GGResIShape.D4b0c2.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b0c2_0_2) = true := by
  rw [show w_D4b0c2_0_2 = .reuse ((GGResIShape.D4b0c2.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c2.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b0c2_1_0) = true := by
  rw [show w_D4b0c2_1_0 = .reuse ((GGResIShape.D4b0c2.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c2.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b0c2_1_1) = true := by
  rw [show w_D4b0c2_1_1 = .reuse ((GGResIShape.D4b0c2.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b0c2_1_2) = true := by
  rw [show w_D4b0c2_1_2 = .reuse ((GGResIShape.D4b0c2.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c2.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b0c2_2_0) = true := by
  rw [show w_D4b0c2_2_0 = .reuse ((GGResIShape.D4b0c2.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c2.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b0c2_2_1) = true := by
  rw [show w_D4b0c2_2_1 = .reuse ((GGResIShape.D4b0c2.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b0c2_2_2) = true := by
  rw [show w_D4b0c2_2_2 = .norm [1, 2, 3, 4] [2, 2, 1, 1, 0] Rq2_4ec79ddb38e2ca04 [0, 1, 2, 3, 1, 0, 4, 0, 1, 3, 2, 1, 0] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [1, 2, 3, 4] [2, 2, 1, 1, 0] Rq2_4ec79ddb38e2ca04 [0, 1, 2, 3, 1, 0, 4, 0, 1, 3, 2, 1, 0] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D4b0c2_2_2

@[expose] def wits_D4b0c2 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b0c2_0_0), (0, 1, w_D4b0c2_0_1), (0, 2, w_D4b0c2_0_2), (1, 0, w_D4b0c2_1_0), (1, 1, w_D4b0c2_1_1), (1, 2, w_D4b0c2_1_2), (2, 0, w_D4b0c2_2_0), (2, 1, w_D4b0c2_2_1), (2, 2, w_D4b0c2_2_2)]

theorem hwits_D4b0c2 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 0 2 (-1) (-1) wits_D4b0c2 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_0_0) (by rfl)]
      exact hcell_D4b0c2_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_0_1) (by rfl)]
      exact hcell_D4b0c2_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_0_2) (by rfl)]
      exact hcell_D4b0c2_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_1_0) (by rfl)]
      exact hcell_D4b0c2_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_1_1) (by rfl)]
      exact hcell_D4b0c2_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_1_2) (by rfl)]
      exact hcell_D4b0c2_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_2_0) (by rfl)]
      exact hcell_D4b0c2_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_2_1) (by rfl)]
      exact hcell_D4b0c2_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2_2_2) (by rfl)]
      exact hcell_D4b0c2_2_2

@[expose] def w_D4b0c2w12_0_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 2, 2, 1, 1]

@[expose] def w_D4b0c2w12_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w12_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w12_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w12_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w12_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w12_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w12_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w12_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w12.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b0c2w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D4b0c2w12_0_0) = true := by
  rw [show w_D4b0c2w12_0_0 = .commonKernel [1, 2, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 2, 1, 1]) (by decide +kernel)

theorem hcell_D4b0c2w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D4b0c2w12_0_1) = true := by
  rw [show w_D4b0c2w12_0_1 = .reuse ((GGResIShape.D4b0c2w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D4b0c2w12_0_2) = true := by
  rw [show w_D4b0c2w12_0_2 = .reuse ((GGResIShape.D4b0c2w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c2w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D4b0c2w12_1_0) = true := by
  rw [show w_D4b0c2w12_1_0 = .reuse ((GGResIShape.D4b0c2w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c2w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D4b0c2w12_1_1) = true := by
  rw [show w_D4b0c2w12_1_1 = .reuse ((GGResIShape.D4b0c2w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D4b0c2w12_1_2) = true := by
  rw [show w_D4b0c2w12_1_2 = .reuse ((GGResIShape.D4b0c2w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c2w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D4b0c2w12_2_0) = true := by
  rw [show w_D4b0c2w12_2_0 = .reuse ((GGResIShape.D4b0c2w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c2w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D4b0c2w12_2_1) = true := by
  rw [show w_D4b0c2w12_2_1 = .reuse ((GGResIShape.D4b0c2w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D4b0c2w12_2_2) = true := by
  rw [show w_D4b0c2w12_2_2 = .reuse ((GGResIShape.D4b0c2w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c2w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b0c2w12 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b0c2w12_0_0), (0, 1, w_D4b0c2w12_0_1), (0, 2, w_D4b0c2w12_0_2), (1, 0, w_D4b0c2w12_1_0), (1, 1, w_D4b0c2w12_1_1), (1, 2, w_D4b0c2w12_1_2), (2, 0, w_D4b0c2w12_2_0), (2, 1, w_D4b0c2w12_2_1), (2, 2, w_D4b0c2w12_2_2)]

theorem hwits_D4b0c2w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 0 2 (-1) (-2) wits_D4b0c2w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_0_0) (by rfl)]
      exact hcell_D4b0c2w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_0_1) (by rfl)]
      exact hcell_D4b0c2w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_0_2) (by rfl)]
      exact hcell_D4b0c2w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_1_0) (by rfl)]
      exact hcell_D4b0c2w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_1_1) (by rfl)]
      exact hcell_D4b0c2w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_1_2) (by rfl)]
      exact hcell_D4b0c2w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_2_0) (by rfl)]
      exact hcell_D4b0c2w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_2_1) (by rfl)]
      exact hcell_D4b0c2w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w12_2_2) (by rfl)]
      exact hcell_D4b0c2w12_2_2

@[expose] def w_D4b0c2w21_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 1, 1, 2, 1]

@[expose] def w_D4b0c2w21_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w21_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w21_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w21_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w21_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w21_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w21_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c2w21_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c2w21.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b0c2w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b0c2w21_0_0) = true := by
  rw [show w_D4b0c2w21_0_0 = .commonKernel [2, 1, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 1, 2, 1]) (by decide +kernel)

theorem hcell_D4b0c2w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b0c2w21_0_1) = true := by
  rw [show w_D4b0c2w21_0_1 = .reuse ((GGResIShape.D4b0c2w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b0c2w21_0_2) = true := by
  rw [show w_D4b0c2w21_0_2 = .reuse ((GGResIShape.D4b0c2w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c2w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b0c2w21_1_0) = true := by
  rw [show w_D4b0c2w21_1_0 = .reuse ((GGResIShape.D4b0c2w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c2w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b0c2w21_1_1) = true := by
  rw [show w_D4b0c2w21_1_1 = .reuse ((GGResIShape.D4b0c2w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b0c2w21_1_2) = true := by
  rw [show w_D4b0c2w21_1_2 = .reuse ((GGResIShape.D4b0c2w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c2w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b0c2w21_2_0) = true := by
  rw [show w_D4b0c2w21_2_0 = .reuse ((GGResIShape.D4b0c2w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c2w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b0c2w21_2_1) = true := by
  rw [show w_D4b0c2w21_2_1 = .reuse ((GGResIShape.D4b0c2w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c2w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c2w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 2 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b0c2w21_2_2) = true := by
  rw [show w_D4b0c2w21_2_2 = .reuse ((GGResIShape.D4b0c2w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c2w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c2w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b0c2w21 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b0c2w21_0_0), (0, 1, w_D4b0c2w21_0_1), (0, 2, w_D4b0c2w21_0_2), (1, 0, w_D4b0c2w21_1_0), (1, 1, w_D4b0c2w21_1_1), (1, 2, w_D4b0c2w21_1_2), (2, 0, w_D4b0c2w21_2_0), (2, 1, w_D4b0c2w21_2_1), (2, 2, w_D4b0c2w21_2_2)]

theorem hwits_D4b0c2w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 0 2 (-2) (-1) wits_D4b0c2w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_0_0) (by rfl)]
      exact hcell_D4b0c2w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_0_1) (by rfl)]
      exact hcell_D4b0c2w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_0_2) (by rfl)]
      exact hcell_D4b0c2w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_1_0) (by rfl)]
      exact hcell_D4b0c2w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_1_1) (by rfl)]
      exact hcell_D4b0c2w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_1_2) (by rfl)]
      exact hcell_D4b0c2w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_2_0) (by rfl)]
      exact hcell_D4b0c2w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_2_1) (by rfl)]
      exact hcell_D4b0c2w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c2w21_2_2) (by rfl)]
      exact hcell_D4b0c2w21_2_2

@[expose] def w_D4b0c3_0_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def pkTab_D4b0c3_2_2 : ℕ := 706582291851786

@[expose] def pkData_D4b0c3_2_2 : List (ℕ × ℕ × ℕ) :=
[(4, 4, 281548012134405),
  (16, 16, 281543729762305),
  (64, 64, 351981176688641),
  (256, 256, 563293567586561),
  (20, 20, 281565179445269),
  (68, 68, 356250445545541),
  (320, 320, 141287261278529),
  (84, 84, 373877045727317),
  (324, 324, 149602658026121),
  (340, 340, 184787352425129)]

@[expose] def w_D4b0c3_2_2 : GGResQTwoCell 4 :=
  .norm [1, 2, 3, 4] [2, 2, 1, 1, 0] Rq2_6585cb8f7470540e [0, 1, 2, 3, 1, 0, 4, 0, 1, 3, 2, 1, 0] 2

open scoped CFSG.Decide.Bounded in
theorem hnorm_D4b0c3_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 4) 0 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [1, 2, 3, 4] Rq2_6585cb8f7470540e [2, 2, 1, 1, 0] [0, 1, 2, 3, 1, 0, 4, 0, 1, 3, 2, 1, 0] 2 := by
  exact GGResQTwoPackedFull.GGResQTwoNormOKK_of_pkF (D := pkData_D4b0c3_2_2) (by decide +kernel)
    (by decide +kernel)
    (GGResQTwoPackedFull.pkListF_std (tab := pkTab_D4b0c3_2_2) (by decide +kernel)
      (by decide +kernel))
    (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D4b0c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b0c3_0_0) = true := by
  rw [show w_D4b0c3_0_0 = .reuse ((GGResIShape.D4b0c3.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c3.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b0c3_0_1) = true := by
  rw [show w_D4b0c3_0_1 = .reuse ((GGResIShape.D4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b0c3_0_2) = true := by
  rw [show w_D4b0c3_0_2 = .reuse ((GGResIShape.D4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b0c3_1_0) = true := by
  rw [show w_D4b0c3_1_0 = .reuse ((GGResIShape.D4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b0c3_1_1) = true := by
  rw [show w_D4b0c3_1_1 = .reuse ((GGResIShape.D4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b0c3_1_2) = true := by
  rw [show w_D4b0c3_1_2 = .reuse ((GGResIShape.D4b0c3.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c3.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b0c3_2_0) = true := by
  rw [show w_D4b0c3_2_0 = .reuse ((GGResIShape.D4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b0c3_2_1) = true := by
  rw [show w_D4b0c3_2_1 = .reuse ((GGResIShape.D4b0c3.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b0c3_2_2) = true := by
  rw [show w_D4b0c3_2_2 = .norm [1, 2, 3, 4] [2, 2, 1, 1, 0] Rq2_6585cb8f7470540e [0, 1, 2, 3, 1, 0, 4, 0, 1, 3, 2, 1, 0] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [1, 2, 3, 4] [2, 2, 1, 1, 0] Rq2_6585cb8f7470540e [0, 1, 2, 3, 1, 0, 4, 0, 1, 3, 2, 1, 0] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D4b0c3_2_2

@[expose] def wits_D4b0c3 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b0c3_0_0), (0, 1, w_D4b0c3_0_1), (0, 2, w_D4b0c3_0_2), (1, 0, w_D4b0c3_1_0), (1, 1, w_D4b0c3_1_1), (1, 2, w_D4b0c3_1_2), (2, 0, w_D4b0c3_2_0), (2, 1, w_D4b0c3_2_1), (2, 2, w_D4b0c3_2_2)]

theorem hwits_D4b0c3 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 0 3 (-1) (-1) wits_D4b0c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_0_0) (by rfl)]
      exact hcell_D4b0c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_0_1) (by rfl)]
      exact hcell_D4b0c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_0_2) (by rfl)]
      exact hcell_D4b0c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_1_0) (by rfl)]
      exact hcell_D4b0c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_1_1) (by rfl)]
      exact hcell_D4b0c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_1_2) (by rfl)]
      exact hcell_D4b0c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_2_0) (by rfl)]
      exact hcell_D4b0c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_2_1) (by rfl)]
      exact hcell_D4b0c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3_2_2) (by rfl)]
      exact hcell_D4b0c3_2_2

@[expose] def w_D4b0c3w12_0_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 2, 1, 2, 1]

@[expose] def w_D4b0c3w12_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w12_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w12_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w12_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w12_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w12_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w12_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w12_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w12.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b0c3w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D4b0c3w12_0_0) = true := by
  rw [show w_D4b0c3w12_0_0 = .commonKernel [1, 2, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 1, 2, 1]) (by decide +kernel)

theorem hcell_D4b0c3w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D4b0c3w12_0_1) = true := by
  rw [show w_D4b0c3w12_0_1 = .reuse ((GGResIShape.D4b0c3w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D4b0c3w12_0_2) = true := by
  rw [show w_D4b0c3w12_0_2 = .reuse ((GGResIShape.D4b0c3w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c3w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D4b0c3w12_1_0) = true := by
  rw [show w_D4b0c3w12_1_0 = .reuse ((GGResIShape.D4b0c3w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c3w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D4b0c3w12_1_1) = true := by
  rw [show w_D4b0c3w12_1_1 = .reuse ((GGResIShape.D4b0c3w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D4b0c3w12_1_2) = true := by
  rw [show w_D4b0c3w12_1_2 = .reuse ((GGResIShape.D4b0c3w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c3w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D4b0c3w12_2_0) = true := by
  rw [show w_D4b0c3w12_2_0 = .reuse ((GGResIShape.D4b0c3w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c3w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D4b0c3w12_2_1) = true := by
  rw [show w_D4b0c3w12_2_1 = .reuse ((GGResIShape.D4b0c3w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D4b0c3w12_2_2) = true := by
  rw [show w_D4b0c3w12_2_2 = .reuse ((GGResIShape.D4b0c3w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c3w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b0c3w12 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b0c3w12_0_0), (0, 1, w_D4b0c3w12_0_1), (0, 2, w_D4b0c3w12_0_2), (1, 0, w_D4b0c3w12_1_0), (1, 1, w_D4b0c3w12_1_1), (1, 2, w_D4b0c3w12_1_2), (2, 0, w_D4b0c3w12_2_0), (2, 1, w_D4b0c3w12_2_1), (2, 2, w_D4b0c3w12_2_2)]

theorem hwits_D4b0c3w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 0 3 (-1) (-2) wits_D4b0c3w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_0_0) (by rfl)]
      exact hcell_D4b0c3w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_0_1) (by rfl)]
      exact hcell_D4b0c3w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_0_2) (by rfl)]
      exact hcell_D4b0c3w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_1_0) (by rfl)]
      exact hcell_D4b0c3w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_1_1) (by rfl)]
      exact hcell_D4b0c3w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_1_2) (by rfl)]
      exact hcell_D4b0c3w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_2_0) (by rfl)]
      exact hcell_D4b0c3w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_2_1) (by rfl)]
      exact hcell_D4b0c3w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w12_2_2) (by rfl)]
      exact hcell_D4b0c3w12_2_2

@[expose] def w_D4b0c3w21_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 1, 2, 1, 1]

@[expose] def w_D4b0c3w21_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w21_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w21_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w21_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w21_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w21_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w21_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b0c3w21_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b0c3w21.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b0c3w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b0c3w21_0_0) = true := by
  rw [show w_D4b0c3w21_0_0 = .commonKernel [2, 1, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 2, 1, 1]) (by decide +kernel)

theorem hcell_D4b0c3w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b0c3w21_0_1) = true := by
  rw [show w_D4b0c3w21_0_1 = .reuse ((GGResIShape.D4b0c3w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b0c3w21_0_2) = true := by
  rw [show w_D4b0c3w21_0_2 = .reuse ((GGResIShape.D4b0c3w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c3w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b0c3w21_1_0) = true := by
  rw [show w_D4b0c3w21_1_0 = .reuse ((GGResIShape.D4b0c3w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c3w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b0c3w21_1_1) = true := by
  rw [show w_D4b0c3w21_1_1 = .reuse ((GGResIShape.D4b0c3w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b0c3w21_1_2) = true := by
  rw [show w_D4b0c3w21_1_2 = .reuse ((GGResIShape.D4b0c3w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c3w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b0c3w21_2_0) = true := by
  rw [show w_D4b0c3w21_2_0 = .reuse ((GGResIShape.D4b0c3w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b0c3w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b0c3w21_2_1) = true := by
  rw [show w_D4b0c3w21_2_1 = .reuse ((GGResIShape.D4b0c3w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b0c3w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b0c3w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 0 3 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b0c3w21_2_2) = true := by
  rw [show w_D4b0c3w21_2_2 = .reuse ((GGResIShape.D4b0c3w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b0c3w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b0c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b0c3w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b0c3w21 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b0c3w21_0_0), (0, 1, w_D4b0c3w21_0_1), (0, 2, w_D4b0c3w21_0_2), (1, 0, w_D4b0c3w21_1_0), (1, 1, w_D4b0c3w21_1_1), (1, 2, w_D4b0c3w21_1_2), (2, 0, w_D4b0c3w21_2_0), (2, 1, w_D4b0c3w21_2_1), (2, 2, w_D4b0c3w21_2_2)]

theorem hwits_D4b0c3w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 0 3 (-2) (-1) wits_D4b0c3w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_0_0) (by rfl)]
      exact hcell_D4b0c3w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_0_1) (by rfl)]
      exact hcell_D4b0c3w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_0_2) (by rfl)]
      exact hcell_D4b0c3w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_1_0) (by rfl)]
      exact hcell_D4b0c3w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_1_1) (by rfl)]
      exact hcell_D4b0c3w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_1_2) (by rfl)]
      exact hcell_D4b0c3w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_2_0) (by rfl)]
      exact hcell_D4b0c3w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_2_1) (by rfl)]
      exact hcell_D4b0c3w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b0c3w21_2_2) (by rfl)]
      exact hcell_D4b0c3w21_2_2

@[expose] def w_D4b2c0_0_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0_1_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 1, 2, 2, 1]

@[expose] def w_D4b2c0_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def pkTab_D4b2c0_2_2 : ℕ := 600479956642314

@[expose] def pkData_D4b2c0_2_2 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 282643224597506),
  (4, 4, 281548012134405),
  (64, 64, 281612432510977),
  (256, 256, 563018958115073),
  (5, 5, 287046645057544),
  (257, 257, 2268029261312),
  (68, 68, 281483654856773),
  (69, 69, 357352105578632),
  (261, 261, 11344647030785),
  (325, 325, 152293796220929)]

@[expose] def w_D4b2c0_2_2 : GGResQTwoCell 4 :=
  .norm [0, 1, 3, 4] [1, 2, 2, 1, 0] Rq2_73c3810ef43f8b4d [2, 1, 0, 3, 1, 2, 4, 2, 1, 3, 0, 1, 2] 3

open scoped CFSG.Decide.Bounded in
theorem hnorm_D4b2c0_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 4) 2 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 3, 4] Rq2_73c3810ef43f8b4d [1, 2, 2, 1, 0] [2, 1, 0, 3, 1, 2, 4, 2, 1, 3, 0, 1, 2] 3 := by
  exact GGResQTwoPackedFull.GGResQTwoNormOKK_of_pkF (D := pkData_D4b2c0_2_2) (by decide +kernel)
    (by decide +kernel)
    (GGResQTwoPackedFull.pkListF_std (tab := pkTab_D4b2c0_2_2) (by decide +kernel)
      (by decide +kernel))
    (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D4b2c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b2c0_0_0) = true := by
  rw [show w_D4b2c0_0_0 = .reuse ((GGResIShape.D4b2c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b2c0_0_1) = true := by
  rw [show w_D4b2c0_0_1 = .reuse ((GGResIShape.D4b2c0.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b2c0_0_2) = true := by
  rw [show w_D4b2c0_0_2 = .reuse ((GGResIShape.D4b2c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b2c0_1_0) = true := by
  rw [show w_D4b2c0_1_0 = .commonKernel [1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D4b2c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b2c0_1_1) = true := by
  rw [show w_D4b2c0_1_1 = .reuse ((GGResIShape.D4b2c0.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b2c0_1_2) = true := by
  rw [show w_D4b2c0_1_2 = .reuse ((GGResIShape.D4b2c0.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c0.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b2c0_2_0) = true := by
  rw [show w_D4b2c0_2_0 = .reuse ((GGResIShape.D4b2c0.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c0.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b2c0_2_1) = true := by
  rw [show w_D4b2c0_2_1 = .reuse ((GGResIShape.D4b2c0.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b2c0_2_2) = true := by
  rw [show w_D4b2c0_2_2 = .norm [0, 1, 3, 4] [1, 2, 2, 1, 0] Rq2_73c3810ef43f8b4d [2, 1, 0, 3, 1, 2, 4, 2, 1, 3, 0, 1, 2] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 3, 4] [1, 2, 2, 1, 0] Rq2_73c3810ef43f8b4d [2, 1, 0, 3, 1, 2, 4, 2, 1, 3, 0, 1, 2] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D4b2c0_2_2

@[expose] def wits_D4b2c0 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b2c0_0_0), (0, 1, w_D4b2c0_0_1), (0, 2, w_D4b2c0_0_2), (1, 0, w_D4b2c0_1_0), (1, 1, w_D4b2c0_1_1), (1, 2, w_D4b2c0_1_2), (2, 0, w_D4b2c0_2_0), (2, 1, w_D4b2c0_2_1), (2, 2, w_D4b2c0_2_2)]

theorem hwits_D4b2c0 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 2 0 (-1) (-1) wits_D4b2c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_0_0) (by rfl)]
      exact hcell_D4b2c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_0_1) (by rfl)]
      exact hcell_D4b2c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_0_2) (by rfl)]
      exact hcell_D4b2c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_1_0) (by rfl)]
      exact hcell_D4b2c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_1_1) (by rfl)]
      exact hcell_D4b2c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_1_2) (by rfl)]
      exact hcell_D4b2c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_2_0) (by rfl)]
      exact hcell_D4b2c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_2_1) (by rfl)]
      exact hcell_D4b2c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0_2_2) (by rfl)]
      exact hcell_D4b2c0_2_2

@[expose] def w_D4b2c0w12_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 2, 1, 1, 1]

@[expose] def w_D4b2c0w12_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w12_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w12_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w12_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w12_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w12_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w12_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w12_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w12.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b2c0w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D4b2c0w12_0_0) = true := by
  rw [show w_D4b2c0w12_0_0 = .commonKernel [2, 2, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 2, 1, 1, 1]) (by decide +kernel)

theorem hcell_D4b2c0w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D4b2c0w12_0_1) = true := by
  rw [show w_D4b2c0w12_0_1 = .reuse ((GGResIShape.D4b2c0w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D4b2c0w12_0_2) = true := by
  rw [show w_D4b2c0w12_0_2 = .reuse ((GGResIShape.D4b2c0w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D4b2c0w12_1_0) = true := by
  rw [show w_D4b2c0w12_1_0 = .reuse ((GGResIShape.D4b2c0w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D4b2c0w12_1_1) = true := by
  rw [show w_D4b2c0w12_1_1 = .reuse ((GGResIShape.D4b2c0w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D4b2c0w12_1_2) = true := by
  rw [show w_D4b2c0w12_1_2 = .reuse ((GGResIShape.D4b2c0w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D4b2c0w12_2_0) = true := by
  rw [show w_D4b2c0w12_2_0 = .reuse ((GGResIShape.D4b2c0w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D4b2c0w12_2_1) = true := by
  rw [show w_D4b2c0w12_2_1 = .reuse ((GGResIShape.D4b2c0w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D4b2c0w12_2_2) = true := by
  rw [show w_D4b2c0w12_2_2 = .reuse ((GGResIShape.D4b2c0w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c0w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b2c0w12 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b2c0w12_0_0), (0, 1, w_D4b2c0w12_0_1), (0, 2, w_D4b2c0w12_0_2), (1, 0, w_D4b2c0w12_1_0), (1, 1, w_D4b2c0w12_1_1), (1, 2, w_D4b2c0w12_1_2), (2, 0, w_D4b2c0w12_2_0), (2, 1, w_D4b2c0w12_2_1), (2, 2, w_D4b2c0w12_2_2)]

theorem hwits_D4b2c0w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 2 0 (-1) (-2) wits_D4b2c0w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_0_0) (by rfl)]
      exact hcell_D4b2c0w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_0_1) (by rfl)]
      exact hcell_D4b2c0w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_0_2) (by rfl)]
      exact hcell_D4b2c0w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_1_0) (by rfl)]
      exact hcell_D4b2c0w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_1_1) (by rfl)]
      exact hcell_D4b2c0w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_1_2) (by rfl)]
      exact hcell_D4b2c0w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_2_0) (by rfl)]
      exact hcell_D4b2c0w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_2_1) (by rfl)]
      exact hcell_D4b2c0w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w12_2_2) (by rfl)]
      exact hcell_D4b2c0w12_2_2

@[expose] def w_D4b2c0w21_0_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 1, 2, 2, 1]

@[expose] def w_D4b2c0w21_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w21_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w21_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w21_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w21_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w21_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w21_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c0w21_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b2c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b2c0w21_0_0) = true := by
  rw [show w_D4b2c0w21_0_0 = .commonKernel [1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D4b2c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b2c0w21_0_1) = true := by
  rw [show w_D4b2c0w21_0_1 = .reuse ((GGResIShape.D4b2c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b2c0w21_0_2) = true := by
  rw [show w_D4b2c0w21_0_2 = .reuse ((GGResIShape.D4b2c0w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b2c0w21_1_0) = true := by
  rw [show w_D4b2c0w21_1_0 = .reuse ((GGResIShape.D4b2c0w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b2c0w21_1_1) = true := by
  rw [show w_D4b2c0w21_1_1 = .reuse ((GGResIShape.D4b2c0w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b2c0w21_1_2) = true := by
  rw [show w_D4b2c0w21_1_2 = .reuse ((GGResIShape.D4b2c0w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c0w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b2c0w21_2_0) = true := by
  rw [show w_D4b2c0w21_2_0 = .reuse ((GGResIShape.D4b2c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b2c0w21_2_1) = true := by
  rw [show w_D4b2c0w21_2_1 = .reuse ((GGResIShape.D4b2c0w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b2c0w21_2_2) = true := by
  rw [show w_D4b2c0w21_2_2 = .reuse ((GGResIShape.D4b2c0w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c0w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b2c0w21 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b2c0w21_0_0), (0, 1, w_D4b2c0w21_0_1), (0, 2, w_D4b2c0w21_0_2), (1, 0, w_D4b2c0w21_1_0), (1, 1, w_D4b2c0w21_1_1), (1, 2, w_D4b2c0w21_1_2), (2, 0, w_D4b2c0w21_2_0), (2, 1, w_D4b2c0w21_2_1), (2, 2, w_D4b2c0w21_2_2)]

theorem hwits_D4b2c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 2 0 (-2) (-1) wits_D4b2c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_0_0) (by rfl)]
      exact hcell_D4b2c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_0_1) (by rfl)]
      exact hcell_D4b2c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_0_2) (by rfl)]
      exact hcell_D4b2c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_1_0) (by rfl)]
      exact hcell_D4b2c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_1_1) (by rfl)]
      exact hcell_D4b2c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_1_2) (by rfl)]
      exact hcell_D4b2c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_2_0) (by rfl)]
      exact hcell_D4b2c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_2_1) (by rfl)]
      exact hcell_D4b2c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c0w21_2_2) (by rfl)]
      exact hcell_D4b2c0w21_2_2

@[expose] def w_D4b2c3_0_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def pkTab_D4b2c3_2_2 : ℕ := 739568177555466

@[expose] def pkData_D4b2c3_2_2 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 281543712969730),
  (4, 4, 281548012134405),
  (64, 64, 351981176688641),
  (256, 256, 563293836021761),
  (5, 5, 281549086918664),
  (68, 68, 356250445545541),
  (320, 320, 141287596822529),
  (69, 69, 357352105578632),
  (324, 324, 149602997764421),
  (325, 325, 151802022466184)]

@[expose] def w_D4b2c3_2_2 : GGResQTwoCell 4 :=
  .norm [0, 1, 3, 4] [1, 2, 2, 1, 0] Rq2_c4bef338e341afc5 [2, 1, 0, 3, 1, 2, 4, 2, 1, 3, 0, 1, 2] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_D4b2c3_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 4) 2 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 3, 4] Rq2_c4bef338e341afc5 [1, 2, 2, 1, 0] [2, 1, 0, 3, 1, 2, 4, 2, 1, 3, 0, 1, 2] 0 := by
  exact GGResQTwoPackedFull.GGResQTwoNormOKK_of_pkF (D := pkData_D4b2c3_2_2) (by decide +kernel)
    (by decide +kernel)
    (GGResQTwoPackedFull.pkListF_std (tab := pkTab_D4b2c3_2_2) (by decide +kernel)
      (by decide +kernel))
    (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D4b2c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b2c3_0_0) = true := by
  rw [show w_D4b2c3_0_0 = .reuse ((GGResIShape.D4b2c3.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c3.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b2c3_0_1) = true := by
  rw [show w_D4b2c3_0_1 = .reuse ((GGResIShape.D4b2c3.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b2c3_0_2) = true := by
  rw [show w_D4b2c3_0_2 = .reuse ((GGResIShape.D4b2c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b2c3_1_0) = true := by
  rw [show w_D4b2c3_1_0 = .reuse ((GGResIShape.D4b2c3.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c3.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b2c3_1_1) = true := by
  rw [show w_D4b2c3_1_1 = .reuse ((GGResIShape.D4b2c3.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b2c3_1_2) = true := by
  rw [show w_D4b2c3_1_2 = .reuse ((GGResIShape.D4b2c3.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c3.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b2c3_2_0) = true := by
  rw [show w_D4b2c3_2_0 = .reuse ((GGResIShape.D4b2c3.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c3.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b2c3_2_1) = true := by
  rw [show w_D4b2c3_2_1 = .reuse ((GGResIShape.D4b2c3.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b2c3_2_2) = true := by
  rw [show w_D4b2c3_2_2 = .norm [0, 1, 3, 4] [1, 2, 2, 1, 0] Rq2_c4bef338e341afc5 [2, 1, 0, 3, 1, 2, 4, 2, 1, 3, 0, 1, 2] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 3, 4] [1, 2, 2, 1, 0] Rq2_c4bef338e341afc5 [2, 1, 0, 3, 1, 2, 4, 2, 1, 3, 0, 1, 2] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D4b2c3_2_2

@[expose] def wits_D4b2c3 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b2c3_0_0), (0, 1, w_D4b2c3_0_1), (0, 2, w_D4b2c3_0_2), (1, 0, w_D4b2c3_1_0), (1, 1, w_D4b2c3_1_1), (1, 2, w_D4b2c3_1_2), (2, 0, w_D4b2c3_2_0), (2, 1, w_D4b2c3_2_1), (2, 2, w_D4b2c3_2_2)]

theorem hwits_D4b2c3 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 2 3 (-1) (-1) wits_D4b2c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_0_0) (by rfl)]
      exact hcell_D4b2c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_0_1) (by rfl)]
      exact hcell_D4b2c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_0_2) (by rfl)]
      exact hcell_D4b2c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_1_0) (by rfl)]
      exact hcell_D4b2c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_1_1) (by rfl)]
      exact hcell_D4b2c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_1_2) (by rfl)]
      exact hcell_D4b2c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_2_0) (by rfl)]
      exact hcell_D4b2c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_2_1) (by rfl)]
      exact hcell_D4b2c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3_2_2) (by rfl)]
      exact hcell_D4b2c3_2_2

@[expose] def w_D4b2c3w12_0_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 2, 1, 2, 1]

@[expose] def w_D4b2c3w12_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w12_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w12_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w12_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w12_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w12_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w12_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w12_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w12.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b2c3w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D4b2c3w12_0_0) = true := by
  rw [show w_D4b2c3w12_0_0 = .commonKernel [1, 2, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 1, 2, 1]) (by decide +kernel)

theorem hcell_D4b2c3w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D4b2c3w12_0_1) = true := by
  rw [show w_D4b2c3w12_0_1 = .reuse ((GGResIShape.D4b2c3w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D4b2c3w12_0_2) = true := by
  rw [show w_D4b2c3w12_0_2 = .reuse ((GGResIShape.D4b2c3w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c3w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D4b2c3w12_1_0) = true := by
  rw [show w_D4b2c3w12_1_0 = .reuse ((GGResIShape.D4b2c3w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c3w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D4b2c3w12_1_1) = true := by
  rw [show w_D4b2c3w12_1_1 = .reuse ((GGResIShape.D4b2c3w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D4b2c3w12_1_2) = true := by
  rw [show w_D4b2c3w12_1_2 = .reuse ((GGResIShape.D4b2c3w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c3w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D4b2c3w12_2_0) = true := by
  rw [show w_D4b2c3w12_2_0 = .reuse ((GGResIShape.D4b2c3w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c3w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D4b2c3w12_2_1) = true := by
  rw [show w_D4b2c3w12_2_1 = .reuse ((GGResIShape.D4b2c3w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D4b2c3w12_2_2) = true := by
  rw [show w_D4b2c3w12_2_2 = .reuse ((GGResIShape.D4b2c3w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c3w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b2c3w12 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b2c3w12_0_0), (0, 1, w_D4b2c3w12_0_1), (0, 2, w_D4b2c3w12_0_2), (1, 0, w_D4b2c3w12_1_0), (1, 1, w_D4b2c3w12_1_1), (1, 2, w_D4b2c3w12_1_2), (2, 0, w_D4b2c3w12_2_0), (2, 1, w_D4b2c3w12_2_1), (2, 2, w_D4b2c3w12_2_2)]

theorem hwits_D4b2c3w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 2 3 (-1) (-2) wits_D4b2c3w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_0_0) (by rfl)]
      exact hcell_D4b2c3w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_0_1) (by rfl)]
      exact hcell_D4b2c3w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_0_2) (by rfl)]
      exact hcell_D4b2c3w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_1_0) (by rfl)]
      exact hcell_D4b2c3w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_1_1) (by rfl)]
      exact hcell_D4b2c3w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_1_2) (by rfl)]
      exact hcell_D4b2c3w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_2_0) (by rfl)]
      exact hcell_D4b2c3w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_2_1) (by rfl)]
      exact hcell_D4b2c3w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w12_2_2) (by rfl)]
      exact hcell_D4b2c3w12_2_2

@[expose] def w_D4b2c3w21_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 1, 2, 1, 1]

@[expose] def w_D4b2c3w21_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w21_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w21_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w21_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w21_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w21_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w21_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b2c3w21_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b2c3w21.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b2c3w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b2c3w21_0_0) = true := by
  rw [show w_D4b2c3w21_0_0 = .commonKernel [2, 1, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 2, 1, 1]) (by decide +kernel)

theorem hcell_D4b2c3w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b2c3w21_0_1) = true := by
  rw [show w_D4b2c3w21_0_1 = .reuse ((GGResIShape.D4b2c3w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b2c3w21_0_2) = true := by
  rw [show w_D4b2c3w21_0_2 = .reuse ((GGResIShape.D4b2c3w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c3w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b2c3w21_1_0) = true := by
  rw [show w_D4b2c3w21_1_0 = .reuse ((GGResIShape.D4b2c3w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c3w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b2c3w21_1_1) = true := by
  rw [show w_D4b2c3w21_1_1 = .reuse ((GGResIShape.D4b2c3w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b2c3w21_1_2) = true := by
  rw [show w_D4b2c3w21_1_2 = .reuse ((GGResIShape.D4b2c3w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c3w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b2c3w21_2_0) = true := by
  rw [show w_D4b2c3w21_2_0 = .reuse ((GGResIShape.D4b2c3w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b2c3w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b2c3w21_2_1) = true := by
  rw [show w_D4b2c3w21_2_1 = .reuse ((GGResIShape.D4b2c3w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b2c3w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b2c3w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 2 3 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b2c3w21_2_2) = true := by
  rw [show w_D4b2c3w21_2_2 = .reuse ((GGResIShape.D4b2c3w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b2c3w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b2c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b2c3w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b2c3w21 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b2c3w21_0_0), (0, 1, w_D4b2c3w21_0_1), (0, 2, w_D4b2c3w21_0_2), (1, 0, w_D4b2c3w21_1_0), (1, 1, w_D4b2c3w21_1_1), (1, 2, w_D4b2c3w21_1_2), (2, 0, w_D4b2c3w21_2_0), (2, 1, w_D4b2c3w21_2_1), (2, 2, w_D4b2c3w21_2_2)]

theorem hwits_D4b2c3w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 2 3 (-2) (-1) wits_D4b2c3w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_0_0) (by rfl)]
      exact hcell_D4b2c3w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_0_1) (by rfl)]
      exact hcell_D4b2c3w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_0_2) (by rfl)]
      exact hcell_D4b2c3w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_1_0) (by rfl)]
      exact hcell_D4b2c3w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_1_1) (by rfl)]
      exact hcell_D4b2c3w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_1_2) (by rfl)]
      exact hcell_D4b2c3w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_2_0) (by rfl)]
      exact hcell_D4b2c3w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_2_1) (by rfl)]
      exact hcell_D4b2c3w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b2c3w21_2_2) (by rfl)]
      exact hcell_D4b2c3w21_2_2

@[expose] def w_D4b3c0_0_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0_1_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 1, 2, 2, 1]

@[expose] def w_D4b3c0_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def pkTab_D4b3c0_2_2 : ℕ := 706582291851786

@[expose] def pkData_D4b3c0_2_2 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 282643224597506),
  (4, 4, 281548012134405),
  (16, 16, 281543729762305),
  (256, 256, 563293567586561),
  (5, 5, 287046645057544),
  (257, 257, 2543711426048),
  (20, 20, 281565179445269),
  (21, 21, 304655999438888),
  (261, 261, 11624619968513),
  (277, 277, 46843608174593)]

@[expose] def w_D4b3c0_2_2 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 4] [2, 1, 2, 1, 0] Rq2_5c2a94249d050724 [3, 1, 0, 2, 1, 3, 4, 3, 1, 2, 0, 1, 3] 2

open scoped CFSG.Decide.Bounded in
theorem hnorm_D4b3c0_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 4) 3 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 4] Rq2_5c2a94249d050724 [2, 1, 2, 1, 0] [3, 1, 0, 2, 1, 3, 4, 3, 1, 2, 0, 1, 3] 2 := by
  exact GGResQTwoPackedFull.GGResQTwoNormOKK_of_pkF (D := pkData_D4b3c0_2_2) (by decide +kernel)
    (by decide +kernel)
    (GGResQTwoPackedFull.pkListF_std (tab := pkTab_D4b3c0_2_2) (by decide +kernel)
      (by decide +kernel))
    (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D4b3c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b3c0_0_0) = true := by
  rw [show w_D4b3c0_0_0 = .reuse ((GGResIShape.D4b3c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b3c0_0_1) = true := by
  rw [show w_D4b3c0_0_1 = .reuse ((GGResIShape.D4b3c0.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b3c0_0_2) = true := by
  rw [show w_D4b3c0_0_2 = .reuse ((GGResIShape.D4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b3c0_1_0) = true := by
  rw [show w_D4b3c0_1_0 = .commonKernel [1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D4b3c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b3c0_1_1) = true := by
  rw [show w_D4b3c0_1_1 = .reuse ((GGResIShape.D4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b3c0_1_2) = true := by
  rw [show w_D4b3c0_1_2 = .reuse ((GGResIShape.D4b3c0.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c0.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b3c0_2_0) = true := by
  rw [show w_D4b3c0_2_0 = .reuse ((GGResIShape.D4b3c0.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c0.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b3c0_2_1) = true := by
  rw [show w_D4b3c0_2_1 = .reuse ((GGResIShape.D4b3c0.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b3c0_2_2) = true := by
  rw [show w_D4b3c0_2_2 = .norm [0, 1, 2, 4] [2, 1, 2, 1, 0] Rq2_5c2a94249d050724 [3, 1, 0, 2, 1, 3, 4, 3, 1, 2, 0, 1, 3] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 4] [2, 1, 2, 1, 0] Rq2_5c2a94249d050724 [3, 1, 0, 2, 1, 3, 4, 3, 1, 2, 0, 1, 3] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D4b3c0_2_2

@[expose] def wits_D4b3c0 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b3c0_0_0), (0, 1, w_D4b3c0_0_1), (0, 2, w_D4b3c0_0_2), (1, 0, w_D4b3c0_1_0), (1, 1, w_D4b3c0_1_1), (1, 2, w_D4b3c0_1_2), (2, 0, w_D4b3c0_2_0), (2, 1, w_D4b3c0_2_1), (2, 2, w_D4b3c0_2_2)]

theorem hwits_D4b3c0 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 3 0 (-1) (-1) wits_D4b3c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_0_0) (by rfl)]
      exact hcell_D4b3c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_0_1) (by rfl)]
      exact hcell_D4b3c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_0_2) (by rfl)]
      exact hcell_D4b3c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_1_0) (by rfl)]
      exact hcell_D4b3c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_1_1) (by rfl)]
      exact hcell_D4b3c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_1_2) (by rfl)]
      exact hcell_D4b3c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_2_0) (by rfl)]
      exact hcell_D4b3c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_2_1) (by rfl)]
      exact hcell_D4b3c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0_2_2) (by rfl)]
      exact hcell_D4b3c0_2_2

@[expose] def w_D4b3c0w12_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 2, 1, 1, 1]

@[expose] def w_D4b3c0w12_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w12_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w12_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w12_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w12_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w12_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w12_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w12_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w12.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b3c0w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D4b3c0w12_0_0) = true := by
  rw [show w_D4b3c0w12_0_0 = .commonKernel [2, 2, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 2, 1, 1, 1]) (by decide +kernel)

theorem hcell_D4b3c0w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D4b3c0w12_0_1) = true := by
  rw [show w_D4b3c0w12_0_1 = .reuse ((GGResIShape.D4b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D4b3c0w12_0_2) = true := by
  rw [show w_D4b3c0w12_0_2 = .reuse ((GGResIShape.D4b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D4b3c0w12_1_0) = true := by
  rw [show w_D4b3c0w12_1_0 = .reuse ((GGResIShape.D4b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D4b3c0w12_1_1) = true := by
  rw [show w_D4b3c0w12_1_1 = .reuse ((GGResIShape.D4b3c0w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D4b3c0w12_1_2) = true := by
  rw [show w_D4b3c0w12_1_2 = .reuse ((GGResIShape.D4b3c0w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D4b3c0w12_2_0) = true := by
  rw [show w_D4b3c0w12_2_0 = .reuse ((GGResIShape.D4b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D4b3c0w12_2_1) = true := by
  rw [show w_D4b3c0w12_2_1 = .reuse ((GGResIShape.D4b3c0w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D4b3c0w12_2_2) = true := by
  rw [show w_D4b3c0w12_2_2 = .reuse ((GGResIShape.D4b3c0w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c0w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b3c0w12 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b3c0w12_0_0), (0, 1, w_D4b3c0w12_0_1), (0, 2, w_D4b3c0w12_0_2), (1, 0, w_D4b3c0w12_1_0), (1, 1, w_D4b3c0w12_1_1), (1, 2, w_D4b3c0w12_1_2), (2, 0, w_D4b3c0w12_2_0), (2, 1, w_D4b3c0w12_2_1), (2, 2, w_D4b3c0w12_2_2)]

theorem hwits_D4b3c0w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 3 0 (-1) (-2) wits_D4b3c0w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_0_0) (by rfl)]
      exact hcell_D4b3c0w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_0_1) (by rfl)]
      exact hcell_D4b3c0w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_0_2) (by rfl)]
      exact hcell_D4b3c0w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_1_0) (by rfl)]
      exact hcell_D4b3c0w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_1_1) (by rfl)]
      exact hcell_D4b3c0w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_1_2) (by rfl)]
      exact hcell_D4b3c0w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_2_0) (by rfl)]
      exact hcell_D4b3c0w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_2_1) (by rfl)]
      exact hcell_D4b3c0w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w12_2_2) (by rfl)]
      exact hcell_D4b3c0w12_2_2

@[expose] def w_D4b3c0w21_0_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 1, 2, 2, 1]

@[expose] def w_D4b3c0w21_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w21_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w21_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w21_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w21_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w21_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w21_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c0w21_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b3c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b3c0w21_0_0) = true := by
  rw [show w_D4b3c0w21_0_0 = .commonKernel [1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D4b3c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b3c0w21_0_1) = true := by
  rw [show w_D4b3c0w21_0_1 = .reuse ((GGResIShape.D4b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b3c0w21_0_2) = true := by
  rw [show w_D4b3c0w21_0_2 = .reuse ((GGResIShape.D4b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b3c0w21_1_0) = true := by
  rw [show w_D4b3c0w21_1_0 = .reuse ((GGResIShape.D4b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b3c0w21_1_1) = true := by
  rw [show w_D4b3c0w21_1_1 = .reuse ((GGResIShape.D4b3c0w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b3c0w21_1_2) = true := by
  rw [show w_D4b3c0w21_1_2 = .reuse ((GGResIShape.D4b3c0w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c0w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b3c0w21_2_0) = true := by
  rw [show w_D4b3c0w21_2_0 = .reuse ((GGResIShape.D4b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b3c0w21_2_1) = true := by
  rw [show w_D4b3c0w21_2_1 = .reuse ((GGResIShape.D4b3c0w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b3c0w21_2_2) = true := by
  rw [show w_D4b3c0w21_2_2 = .reuse ((GGResIShape.D4b3c0w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c0w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b3c0w21 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b3c0w21_0_0), (0, 1, w_D4b3c0w21_0_1), (0, 2, w_D4b3c0w21_0_2), (1, 0, w_D4b3c0w21_1_0), (1, 1, w_D4b3c0w21_1_1), (1, 2, w_D4b3c0w21_1_2), (2, 0, w_D4b3c0w21_2_0), (2, 1, w_D4b3c0w21_2_1), (2, 2, w_D4b3c0w21_2_2)]

theorem hwits_D4b3c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 3 0 (-2) (-1) wits_D4b3c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_0_0) (by rfl)]
      exact hcell_D4b3c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_0_1) (by rfl)]
      exact hcell_D4b3c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_0_2) (by rfl)]
      exact hcell_D4b3c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_1_0) (by rfl)]
      exact hcell_D4b3c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_1_1) (by rfl)]
      exact hcell_D4b3c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_1_2) (by rfl)]
      exact hcell_D4b3c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_2_0) (by rfl)]
      exact hcell_D4b3c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_2_1) (by rfl)]
      exact hcell_D4b3c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c0w21_2_2) (by rfl)]
      exact hcell_D4b3c0w21_2_2

@[expose] def w_D4b3c2_0_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2_1_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 1, 1, 2, 1]

@[expose] def w_D4b3c2_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def pkTab_D4b3c2_2_2 : ℕ := 739568177555466

@[expose] def pkData_D4b3c2_2_2 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 281543712969730),
  (4, 4, 281548012134405),
  (16, 16, 299135915806721),
  (256, 256, 563293836021761),
  (5, 5, 281549086918664),
  (20, 20, 303555412000789),
  (272, 272, 35545686495233),
  (21, 21, 304655999438888),
  (276, 276, 44641907409173),
  (277, 277, 46843077595688)]

@[expose] def w_D4b3c2_2_2 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 4] [2, 1, 2, 1, 0] Rq2_3de60cfe5fc0fe41 [3, 1, 0, 2, 1, 3, 4, 3, 1, 2, 0, 1, 3] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_D4b3c2_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 4) 3 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 4] Rq2_3de60cfe5fc0fe41 [2, 1, 2, 1, 0] [3, 1, 0, 2, 1, 3, 4, 3, 1, 2, 0, 1, 3] 0 := by
  exact GGResQTwoPackedFull.GGResQTwoNormOKK_of_pkF (D := pkData_D4b3c2_2_2) (by decide +kernel)
    (by decide +kernel)
    (GGResQTwoPackedFull.pkListF_std (tab := pkTab_D4b3c2_2_2) (by decide +kernel)
      (by decide +kernel))
    (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D4b3c2_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b3c2_0_0) = true := by
  rw [show w_D4b3c2_0_0 = .reuse ((GGResIShape.D4b3c2.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c2.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b3c2_0_1) = true := by
  rw [show w_D4b3c2_0_1 = .reuse ((GGResIShape.D4b3c2.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b3c2_0_2) = true := by
  rw [show w_D4b3c2_0_2 = .reuse ((GGResIShape.D4b3c2.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c2.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b3c2_1_0) = true := by
  rw [show w_D4b3c2_1_0 = .commonKernel [2, 1, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 1, 2, 1]) (by decide +kernel)

theorem hcell_D4b3c2_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b3c2_1_1) = true := by
  rw [show w_D4b3c2_1_1 = .reuse ((GGResIShape.D4b3c2.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b3c2_1_2) = true := by
  rw [show w_D4b3c2_1_2 = .reuse ((GGResIShape.D4b3c2.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c2.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b3c2_2_0) = true := by
  rw [show w_D4b3c2_2_0 = .reuse ((GGResIShape.D4b3c2.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c2.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b3c2_2_1) = true := by
  rw [show w_D4b3c2_2_1 = .reuse ((GGResIShape.D4b3c2.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b3c2_2_2) = true := by
  rw [show w_D4b3c2_2_2 = .norm [0, 1, 2, 4] [2, 1, 2, 1, 0] Rq2_3de60cfe5fc0fe41 [3, 1, 0, 2, 1, 3, 4, 3, 1, 2, 0, 1, 3] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 4] [2, 1, 2, 1, 0] Rq2_3de60cfe5fc0fe41 [3, 1, 0, 2, 1, 3, 4, 3, 1, 2, 0, 1, 3] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D4b3c2_2_2

@[expose] def wits_D4b3c2 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b3c2_0_0), (0, 1, w_D4b3c2_0_1), (0, 2, w_D4b3c2_0_2), (1, 0, w_D4b3c2_1_0), (1, 1, w_D4b3c2_1_1), (1, 2, w_D4b3c2_1_2), (2, 0, w_D4b3c2_2_0), (2, 1, w_D4b3c2_2_1), (2, 2, w_D4b3c2_2_2)]

theorem hwits_D4b3c2 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 3 2 (-1) (-1) wits_D4b3c2 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_0_0) (by rfl)]
      exact hcell_D4b3c2_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_0_1) (by rfl)]
      exact hcell_D4b3c2_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_0_2) (by rfl)]
      exact hcell_D4b3c2_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_1_0) (by rfl)]
      exact hcell_D4b3c2_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_1_1) (by rfl)]
      exact hcell_D4b3c2_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_1_2) (by rfl)]
      exact hcell_D4b3c2_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_2_0) (by rfl)]
      exact hcell_D4b3c2_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_2_1) (by rfl)]
      exact hcell_D4b3c2_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2_2_2) (by rfl)]
      exact hcell_D4b3c2_2_2

@[expose] def w_D4b3c2w12_0_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 2, 2, 1, 1]

@[expose] def w_D4b3c2w12_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w12_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w12_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w12_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w12_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w12_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w12_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w12_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w12.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b3c2w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D4b3c2w12_0_0) = true := by
  rw [show w_D4b3c2w12_0_0 = .commonKernel [1, 2, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 2, 1, 1]) (by decide +kernel)

theorem hcell_D4b3c2w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D4b3c2w12_0_1) = true := by
  rw [show w_D4b3c2w12_0_1 = .reuse ((GGResIShape.D4b3c2w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D4b3c2w12_0_2) = true := by
  rw [show w_D4b3c2w12_0_2 = .reuse ((GGResIShape.D4b3c2w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c2w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D4b3c2w12_1_0) = true := by
  rw [show w_D4b3c2w12_1_0 = .reuse ((GGResIShape.D4b3c2w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c2w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D4b3c2w12_1_1) = true := by
  rw [show w_D4b3c2w12_1_1 = .reuse ((GGResIShape.D4b3c2w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D4b3c2w12_1_2) = true := by
  rw [show w_D4b3c2w12_1_2 = .reuse ((GGResIShape.D4b3c2w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c2w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D4b3c2w12_2_0) = true := by
  rw [show w_D4b3c2w12_2_0 = .reuse ((GGResIShape.D4b3c2w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c2w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D4b3c2w12_2_1) = true := by
  rw [show w_D4b3c2w12_2_1 = .reuse ((GGResIShape.D4b3c2w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D4b3c2w12_2_2) = true := by
  rw [show w_D4b3c2w12_2_2 = .reuse ((GGResIShape.D4b3c2w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c2w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b3c2w12 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b3c2w12_0_0), (0, 1, w_D4b3c2w12_0_1), (0, 2, w_D4b3c2w12_0_2), (1, 0, w_D4b3c2w12_1_0), (1, 1, w_D4b3c2w12_1_1), (1, 2, w_D4b3c2w12_1_2), (2, 0, w_D4b3c2w12_2_0), (2, 1, w_D4b3c2w12_2_1), (2, 2, w_D4b3c2w12_2_2)]

theorem hwits_D4b3c2w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 3 2 (-1) (-2) wits_D4b3c2w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_0_0) (by rfl)]
      exact hcell_D4b3c2w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_0_1) (by rfl)]
      exact hcell_D4b3c2w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_0_2) (by rfl)]
      exact hcell_D4b3c2w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_1_0) (by rfl)]
      exact hcell_D4b3c2w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_1_1) (by rfl)]
      exact hcell_D4b3c2w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_1_2) (by rfl)]
      exact hcell_D4b3c2w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_2_0) (by rfl)]
      exact hcell_D4b3c2w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_2_1) (by rfl)]
      exact hcell_D4b3c2w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w12_2_2) (by rfl)]
      exact hcell_D4b3c2w12_2_2

@[expose] def w_D4b3c2w21_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 1, 1, 2, 1]

@[expose] def w_D4b3c2w21_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w21_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w21_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w21_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w21_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w21_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w21_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D4b3c2w21_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.D4b3c2w21.cell3.getD 8 (0, 0, .o2b)).2.2)

theorem hcell_D4b3c2w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D4b3c2w21_0_0) = true := by
  rw [show w_D4b3c2w21_0_0 = .commonKernel [2, 1, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 1, 2, 1]) (by decide +kernel)

theorem hcell_D4b3c2w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D4b3c2w21_0_1) = true := by
  rw [show w_D4b3c2w21_0_1 = .reuse ((GGResIShape.D4b3c2w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D4b3c2w21_0_2) = true := by
  rw [show w_D4b3c2w21_0_2 = .reuse ((GGResIShape.D4b3c2w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c2w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D4b3c2w21_1_0) = true := by
  rw [show w_D4b3c2w21_1_0 = .reuse ((GGResIShape.D4b3c2w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c2w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D4b3c2w21_1_1) = true := by
  rw [show w_D4b3c2w21_1_1 = .reuse ((GGResIShape.D4b3c2w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D4b3c2w21_1_2) = true := by
  rw [show w_D4b3c2w21_1_2 = .reuse ((GGResIShape.D4b3c2w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c2w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D4b3c2w21_2_0) = true := by
  rw [show w_D4b3c2w21_2_0 = .reuse ((GGResIShape.D4b3c2w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D4b3c2w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D4b3c2w21_2_1) = true := by
  rw [show w_D4b3c2w21_2_1 = .reuse ((GGResIShape.D4b3c2w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D4b3c2w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D4b3c2w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 4) 3 2 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D4b3c2w21_2_2) = true := by
  rw [show w_D4b3c2w21_2_2 = .reuse ((GGResIShape.D4b3c2w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D4b3c2w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D4b3c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D4b3c2w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D4b3c2w21 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_D4b3c2w21_0_0), (0, 1, w_D4b3c2w21_0_1), (0, 2, w_D4b3c2w21_0_2), (1, 0, w_D4b3c2w21_1_0), (1, 1, w_D4b3c2w21_1_1), (1, 2, w_D4b3c2w21_1_2), (2, 0, w_D4b3c2w21_2_0), (2, 1, w_D4b3c2w21_2_1), (2, 2, w_D4b3c2w21_2_2)]

theorem hwits_D4b3c2w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 4) 3 2 (-2) (-1) wits_D4b3c2w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_0_0) (by rfl)]
      exact hcell_D4b3c2w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_0_1) (by rfl)]
      exact hcell_D4b3c2w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_0_2) (by rfl)]
      exact hcell_D4b3c2w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_1_0) (by rfl)]
      exact hcell_D4b3c2w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_1_1) (by rfl)]
      exact hcell_D4b3c2w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_1_2) (by rfl)]
      exact hcell_D4b3c2w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_2_0) (by rfl)]
      exact hcell_D4b3c2w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_2_1) (by rfl)]
      exact hcell_D4b3c2w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D4b3c2w21_2_2) (by rfl)]
      exact hcell_D4b3c2w21_2_2

@[expose] def wits_D4_b0 (s : Fin 4 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 4) :=
  if s = (2, -1, -1) then wits_D4b0c2
  else if s = (2, -1, -2) then wits_D4b0c2w12
  else if s = (2, -2, -1) then wits_D4b0c2w21
  else if s = (3, -1, -1) then wits_D4b0c3
  else if s = (3, -1, -2) then wits_D4b0c3w12
  else if s = (3, -2, -1) then wits_D4b0c3w21
  else []

theorem cell_D4_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.D 4) 0 (GGResIDisp.D4.shapes_D4_b0) (wits_D4_b0) := by
  intro s hs
  simp only [GGResIDisp.D4.shapes_D4_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_D4_b0, if_pos rfl]
    exact hwits_D4b0c2
  · simp only [wits_D4_b0, if_neg (by decide : ¬ (((2, -1, -2)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_D4b0c2w12
  · simp only [wits_D4_b0, if_neg (by decide : ¬ (((2, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((2, -1, -2)))), if_pos rfl]
    exact hwits_D4b0c2w21
  · simp only [wits_D4_b0, if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -2, -1)))), if_pos rfl]
    exact hwits_D4b0c3
  · simp only [wits_D4_b0, if_neg (by decide : ¬ (((3, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((2, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((2, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_D4b0c3w12
  · simp only [wits_D4_b0, if_neg (by decide : ¬ (((3, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((2, -1, -2)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((2, -2, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((3, -1, -2)))), if_pos rfl]
    exact hwits_D4b0c3w21
theorem hsideOK_D4_b0 :
    ∀ s ∈ GGResIDisp.D4.shapes_D4_b0, ∀ w ∈ wits_D4_b0 s,
      ggResQTwoCellSideOK (0 : Fin 4) w.2.2 := by
  have hall : (GGResIDisp.D4.shapes_D4_b0.all fun s => (wits_D4_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 4) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D4_b0 :
    ∀ s ∈ GGResIDisp.D4.shapes_D4_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D4.shapes_D4_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def wits_D4_b2 (s : Fin 4 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 4) :=
  if s = (0, -1, -1) then wits_D4b2c0
  else if s = (0, -1, -2) then wits_D4b2c0w12
  else if s = (0, -2, -1) then wits_D4b2c0w21
  else if s = (3, -1, -1) then wits_D4b2c3
  else if s = (3, -1, -2) then wits_D4b2c3w12
  else if s = (3, -2, -1) then wits_D4b2c3w21
  else []

theorem cell_D4_b2 :
    GGResQTwoShapeCoverage (CartanMatrix.D 4) 2 (GGResIDisp.D4.shapes_D4_b2) (wits_D4_b2) := by
  intro s hs
  simp only [GGResIDisp.D4.shapes_D4_b2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_D4_b2, if_pos rfl]
    exact hwits_D4b2c0
  · simp only [wits_D4_b2, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_D4b2c0w12
  · simp only [wits_D4_b2, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_D4b2c0w21
  · simp only [wits_D4_b2, if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_D4b2c3
  · simp only [wits_D4_b2, if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_D4b2c3w12
  · simp only [wits_D4_b2, if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((3, -1, -2)))), if_pos rfl]
    exact hwits_D4b2c3w21
theorem hsideOK_D4_b2 :
    ∀ s ∈ GGResIDisp.D4.shapes_D4_b2, ∀ w ∈ wits_D4_b2 s,
      ggResQTwoCellSideOK (2 : Fin 4) w.2.2 := by
  have hall : (GGResIDisp.D4.shapes_D4_b2.all fun s => (wits_D4_b2 s).all fun w =>
      ggResQTwoCellSideOKB (2 : Fin 4) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D4_b2 :
    ∀ s ∈ GGResIDisp.D4.shapes_D4_b2, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D4.shapes_D4_b2.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def wits_D4_b3 (s : Fin 4 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 4) :=
  if s = (0, -1, -1) then wits_D4b3c0
  else if s = (0, -1, -2) then wits_D4b3c0w12
  else if s = (0, -2, -1) then wits_D4b3c0w21
  else if s = (2, -1, -1) then wits_D4b3c2
  else if s = (2, -1, -2) then wits_D4b3c2w12
  else if s = (2, -2, -1) then wits_D4b3c2w21
  else []

theorem cell_D4_b3 :
    GGResQTwoShapeCoverage (CartanMatrix.D 4) 3 (GGResIDisp.D4.shapes_D4_b3) (wits_D4_b3) := by
  intro s hs
  simp only [GGResIDisp.D4.shapes_D4_b3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_D4_b3, if_pos rfl]
    exact hwits_D4b3c0
  · simp only [wits_D4_b3, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_D4b3c0w12
  · simp only [wits_D4_b3, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_D4b3c0w21
  · simp only [wits_D4_b3, if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_D4b3c2
  · simp only [wits_D4_b3, if_neg (by decide : ¬ (((2, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -1, -2)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_D4b3c2w12
  · simp only [wits_D4_b3, if_neg (by decide : ¬ (((2, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((2, -1, -2)))), if_pos rfl]
    exact hwits_D4b3c2w21
theorem hsideOK_D4_b3 :
    ∀ s ∈ GGResIDisp.D4.shapes_D4_b3, ∀ w ∈ wits_D4_b3 s,
      ggResQTwoCellSideOK (3 : Fin 4) w.2.2 := by
  have hall : (GGResIDisp.D4.shapes_D4_b3.all fun s => (wits_D4_b3 s).all fun w =>
      ggResQTwoCellSideOKB (3 : Fin 4) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D4_b3 :
    ∀ s ∈ GGResIDisp.D4.shapes_D4_b3, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D4.shapes_D4_b3.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataD4
