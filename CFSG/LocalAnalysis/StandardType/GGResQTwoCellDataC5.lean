module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataC5

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_2bc4de22acabb593 : List (Fin 6 × List (Fin 6)) :=
[(0, []), (1, []), (2, []), (3, []), (4, []), (0, [1]), (1, [2]), (2, [3]), (3, [4]), (4, [3]), (0, [2, 1]), (1, [3, 2]), (2, [4, 3]), (4, [2, 3]), (0, [3, 2, 1]), (1, [4, 3, 2]), (2, [3, 4, 3]), (4, [1, 2, 3]), (0, [4, 3, 2, 1]), (1, [3, 4, 3, 2]), (4, [0, 1, 2, 3]), (0, [3, 4, 3, 2, 1]), (1, [2, 3, 4, 3, 2]), (0, [2, 3, 4, 3, 2, 1]), (0, [1, 2, 3, 4, 3, 2, 1])]

@[expose] def pkTabC5 : ℕ := 634040428308490

@[expose] def pkDataC5 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 281543712969730),
  (4, 4, 281543717167109),
  (16, 16, 281560909631489),
  (64, 64, 351981243731969),
  (256, 256, 563568445493249),
  (5, 5, 281543718209544),
  (20, 20, 281565179445269),
  (80, 80, 369470400974849),
  (320, 576, 703756782014465),
  (384, 320, 281887981441025),
  (21, 21, 281566255255592),
  (84, 84, 373876920057941),
  (336, 592, 739576591765505),
  (416, 336, 281544065978369),
  (85, 85, 374978579009704),
  (340, 596, 748376593695317),
  (400, 656, 281921670762497),
  (424, 340, 281543713317545),
  (341, 597, 750576690270632),
  (404, 660, 281930952442517),
  (426, 341, 281543712969046),
  (405, 661, 281933100618088),
  (420, 676, 281544073679525),
  (421, 677, 281544076469592),
  (425, 681, 281543713318913)]

theorem pkTabC5_spec : ∀ a b : Fin 5, ((CartanMatrix.C 5 a b : ℤ) : ZMod 3) =
    ((GGResQTwoPacked.pkLane pkTabC5 (a.val * 5 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedC5 : GGResQTwoPacked.pkSharedOK pkTabC5 5 ([0, 1, 2, 3, 4] : List (Fin 6))
    Rq2_2bc4de22acabb593 pkDataC5 = true := by
  decide +kernel

theorem pkListC5 (ib ic : Fin 5) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.C 5) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.C 5) ib ic e₁ e₂ u v k).get
      (Fin.last 6) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.C 5) ib ic e₁ e₂ u v)
        [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 ∧
      ∀ r ∈ Rq2_2bc4de22acabb593, ∃ d ∈ pkDataC5, GGResQTwoPacked.pkBlkM 5
        (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.C 5) ib ic e₁ e₂ u v) r) = d.2.2 :=
  GGResQTwoPacked.pkShared_sound pkSharedC5 (GGResQTwoPacked.pkTab_std pkTabC5_spec ib ic e₁ e₂ u v)
    h2 hx

@[expose] def w_C5b4c0_0_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0_0_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 0, 1, 2, 0, 1]

@[expose] def w_C5b4c0_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0_1_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 0, 1, 2, 0, 1]

@[expose] def w_C5b4c0_1_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [0, 2, 1, 0, 2, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 5, 4, 5, 3, 4, 0, 5] 1

@[expose] def w_C5b4c0_2_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 1, 1, 1, 1, 1]

@[expose] def w_C5b4c0_2_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 0, 1, 2, 0, 1]

@[expose] def w_C5b4c0_2_2 : GGResQTwoCell 5 :=
  .commonKernel [0, 2, 1, 0, 2, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_C5b4c0_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 5) 4 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 [0, 2, 1, 0, 2, 1] [5, 0, 4, 3, 5, 4, 5, 3, 4, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC5) (by decide +kernel)
    (by decide +kernel) (pkListC5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C5b4c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C5b4c0_0_0) = true := by
  rw [show w_C5b4c0_0_0 = .reuse ((GGResIShape.C5b4c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C5b4c0_0_1) = true := by
  rw [show w_C5b4c0_0_1 = .commonKernel [2, 0, 1, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 0, 1]) (by decide +kernel)

theorem hcell_C5b4c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C5b4c0_0_2) = true := by
  rw [show w_C5b4c0_0_2 = .reuse ((GGResIShape.C5b4c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C5b4c0_1_0) = true := by
  rw [show w_C5b4c0_1_0 = .reuse ((GGResIShape.C5b4c0.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c0.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C5b4c0_1_1) = true := by
  rw [show w_C5b4c0_1_1 = .commonKernel [2, 0, 1, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 0, 1]) (by decide +kernel)

theorem hcell_C5b4c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C5b4c0_1_2) = true := by
  rw [show w_C5b4c0_1_2 = .norm [0, 1, 2, 3, 4] [0, 2, 1, 0, 2, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 5, 4, 5, 3, 4, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [0, 2, 1, 0, 2, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 5, 4, 5, 3, 4, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C5b4c0_1_2

theorem hcell_C5b4c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C5b4c0_2_0) = true := by
  rw [show w_C5b4c0_2_0 = .commonKernel [1, 1, 1, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 1, 1]) (by decide +kernel)

theorem hcell_C5b4c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C5b4c0_2_1) = true := by
  rw [show w_C5b4c0_2_1 = .commonKernel [2, 0, 1, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 0, 1]) (by decide +kernel)

theorem hcell_C5b4c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C5b4c0_2_2) = true := by
  rw [show w_C5b4c0_2_2 = .commonKernel [0, 2, 1, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 1, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_C5b4c0 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_C5b4c0_0_0), (0, 1, w_C5b4c0_0_1), (0, 2, w_C5b4c0_0_2), (1, 0, w_C5b4c0_1_0), (1, 1, w_C5b4c0_1_1), (1, 2, w_C5b4c0_1_2), (2, 0, w_C5b4c0_2_0), (2, 1, w_C5b4c0_2_1), (2, 2, w_C5b4c0_2_2)]

theorem hwits_C5b4c0 :
    GGResQTwoCellCheckAll (CartanMatrix.C 5) 4 0 (-1) (-1) wits_C5b4c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_0_0) (by rfl)]
      exact hcell_C5b4c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_0_1) (by rfl)]
      exact hcell_C5b4c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_0_2) (by rfl)]
      exact hcell_C5b4c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_1_0) (by rfl)]
      exact hcell_C5b4c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_1_1) (by rfl)]
      exact hcell_C5b4c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_1_2) (by rfl)]
      exact hcell_C5b4c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_2_0) (by rfl)]
      exact hcell_C5b4c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_2_1) (by rfl)]
      exact hcell_C5b4c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0_2_2) (by rfl)]
      exact hcell_C5b4c0_2_2

@[expose] def w_C5b4c0w12_0_0 : GGResQTwoCell 5 :=
  .commonKernel [2, 2, 2, 2, 2, 1]

@[expose] def w_C5b4c0w12_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w12_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w12_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w12_1_1 : GGResQTwoCell 5 :=
  .commonKernel [0, 1, 2, 0, 1, 1]

@[expose] def w_C5b4c0w12_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w12_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w12_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w12_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 0, 2, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 4, 5, 4, 3, 4, 0, 5] 1

open scoped CFSG.Decide.Bounded in
theorem hnorm_C5b4c0w12_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 5) 4 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 [1, 0, 2, 1, 0, 1] [5, 0, 4, 3, 4, 5, 4, 3, 4, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC5) (by decide +kernel)
    (by decide +kernel) (pkListC5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C5b4c0w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_C5b4c0w12_0_0) = true := by
  rw [show w_C5b4c0w12_0_0 = .commonKernel [2, 2, 2, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 2, 2, 2, 2, 1]) (by decide +kernel)

theorem hcell_C5b4c0w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_C5b4c0w12_0_1) = true := by
  rw [show w_C5b4c0w12_0_1 = .reuse ((GGResIShape.C5b4c0w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_C5b4c0w12_0_2) = true := by
  rw [show w_C5b4c0w12_0_2 = .reuse ((GGResIShape.C5b4c0w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_C5b4c0w12_1_0) = true := by
  rw [show w_C5b4c0w12_1_0 = .reuse ((GGResIShape.C5b4c0w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_C5b4c0w12_1_1) = true := by
  rw [show w_C5b4c0w12_1_1 = .commonKernel [0, 1, 2, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 1, 2, 0, 1, 1]) (by decide +kernel)

theorem hcell_C5b4c0w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_C5b4c0w12_1_2) = true := by
  rw [show w_C5b4c0w12_1_2 = .reuse ((GGResIShape.C5b4c0w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_C5b4c0w12_2_0) = true := by
  rw [show w_C5b4c0w12_2_0 = .reuse ((GGResIShape.C5b4c0w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_C5b4c0w12_2_1) = true := by
  rw [show w_C5b4c0w12_2_1 = .reuse ((GGResIShape.C5b4c0w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c0w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_C5b4c0w12_2_2) = true := by
  rw [show w_C5b4c0w12_2_2 = .norm [0, 1, 2, 3, 4] [1, 0, 2, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 4, 5, 4, 3, 4, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 0, 2, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 4, 5, 4, 3, 4, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C5b4c0w12_2_2

@[expose] def wits_C5b4c0w12 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_C5b4c0w12_0_0), (0, 1, w_C5b4c0w12_0_1), (0, 2, w_C5b4c0w12_0_2), (1, 0, w_C5b4c0w12_1_0), (1, 1, w_C5b4c0w12_1_1), (1, 2, w_C5b4c0w12_1_2), (2, 0, w_C5b4c0w12_2_0), (2, 1, w_C5b4c0w12_2_1), (2, 2, w_C5b4c0w12_2_2)]

theorem hwits_C5b4c0w12 :
    GGResQTwoCellCheckAll (CartanMatrix.C 5) 4 0 (-1) (-2) wits_C5b4c0w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_0_0) (by rfl)]
      exact hcell_C5b4c0w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_0_1) (by rfl)]
      exact hcell_C5b4c0w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_0_2) (by rfl)]
      exact hcell_C5b4c0w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_1_0) (by rfl)]
      exact hcell_C5b4c0w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_1_1) (by rfl)]
      exact hcell_C5b4c0w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_1_2) (by rfl)]
      exact hcell_C5b4c0w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_2_0) (by rfl)]
      exact hcell_C5b4c0w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_2_1) (by rfl)]
      exact hcell_C5b4c0w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w12_2_2) (by rfl)]
      exact hcell_C5b4c0w12_2_2

@[expose] def w_C5b4c0w21_0_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 1, 1, 1, 1, 1]

@[expose] def w_C5b4c0w21_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w21_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w21_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w21_1_1 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [2, 0, 1, 2, 0, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 4, 5, 4, 3, 4, 0, 5] 1

@[expose] def w_C5b4c0w21_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w21_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w21_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c0w21_2_2 : GGResQTwoCell 5 :=
  .commonKernel [0, 2, 1, 0, 2, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_C5b4c0w21_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 5) 4 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 [2, 0, 1, 2, 0, 1] [5, 0, 4, 3, 4, 5, 4, 3, 4, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC5) (by decide +kernel)
    (by decide +kernel) (pkListC5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C5b4c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C5b4c0w21_0_0) = true := by
  rw [show w_C5b4c0w21_0_0 = .commonKernel [1, 1, 1, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 1, 1]) (by decide +kernel)

theorem hcell_C5b4c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C5b4c0w21_0_1) = true := by
  rw [show w_C5b4c0w21_0_1 = .reuse ((GGResIShape.C5b4c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C5b4c0w21_0_2) = true := by
  rw [show w_C5b4c0w21_0_2 = .reuse ((GGResIShape.C5b4c0w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C5b4c0w21_1_0) = true := by
  rw [show w_C5b4c0w21_1_0 = .reuse ((GGResIShape.C5b4c0w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C5b4c0w21_1_1) = true := by
  rw [show w_C5b4c0w21_1_1 = .norm [0, 1, 2, 3, 4] [2, 0, 1, 2, 0, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 4, 5, 4, 3, 4, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [2, 0, 1, 2, 0, 1] Rq2_2bc4de22acabb593 [5, 0, 4, 3, 4, 5, 4, 3, 4, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C5b4c0w21_1_1

theorem hcell_C5b4c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C5b4c0w21_1_2) = true := by
  rw [show w_C5b4c0w21_1_2 = .reuse ((GGResIShape.C5b4c0w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c0w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C5b4c0w21_2_0) = true := by
  rw [show w_C5b4c0w21_2_0 = .reuse ((GGResIShape.C5b4c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C5b4c0w21_2_1) = true := by
  rw [show w_C5b4c0w21_2_1 = .reuse ((GGResIShape.C5b4c0w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c0w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C5b4c0w21_2_2) = true := by
  rw [show w_C5b4c0w21_2_2 = .commonKernel [0, 2, 1, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 1, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_C5b4c0w21 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_C5b4c0w21_0_0), (0, 1, w_C5b4c0w21_0_1), (0, 2, w_C5b4c0w21_0_2), (1, 0, w_C5b4c0w21_1_0), (1, 1, w_C5b4c0w21_1_1), (1, 2, w_C5b4c0w21_1_2), (2, 0, w_C5b4c0w21_2_0), (2, 1, w_C5b4c0w21_2_1), (2, 2, w_C5b4c0w21_2_2)]

theorem hwits_C5b4c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.C 5) 4 0 (-2) (-1) wits_C5b4c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_0_0) (by rfl)]
      exact hcell_C5b4c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_0_1) (by rfl)]
      exact hcell_C5b4c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_0_2) (by rfl)]
      exact hcell_C5b4c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_1_0) (by rfl)]
      exact hcell_C5b4c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_1_1) (by rfl)]
      exact hcell_C5b4c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_1_2) (by rfl)]
      exact hcell_C5b4c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_2_0) (by rfl)]
      exact hcell_C5b4c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_2_1) (by rfl)]
      exact hcell_C5b4c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c0w21_2_2) (by rfl)]
      exact hcell_C5b4c0w21_2_2

@[expose] def w_C5b4c1_0_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 2, 2, 2, 2, 1]

@[expose] def w_C5b4c1_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c1.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c1_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c1.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c1_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c1.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c1_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c1.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c1_1_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [0, 0, 2, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 1, 4, 3, 5, 4, 5, 3, 4, 1, 5] 0

@[expose] def w_C5b4c1_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c1.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c1_2_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 2, 0, 1, 1]

@[expose] def w_C5b4c1_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c1.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C5b4c1_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 5) 4 1 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 [0, 0, 2, 1, 0, 1] [5, 1, 4, 3, 5, 4, 5, 3, 4, 1, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC5) (by decide +kernel)
    (by decide +kernel) (pkListC5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C5b4c1_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C5b4c1_0_0) = true := by
  rw [show w_C5b4c1_0_0 = .commonKernel [1, 2, 2, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 2, 2, 2, 1]) (by decide +kernel)

theorem hcell_C5b4c1_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C5b4c1_0_1) = true := by
  rw [show w_C5b4c1_0_1 = .reuse ((GGResIShape.C5b4c1.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c1.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c1.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c1_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C5b4c1_0_2) = true := by
  rw [show w_C5b4c1_0_2 = .reuse ((GGResIShape.C5b4c1.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c1.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c1.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c1_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C5b4c1_1_0) = true := by
  rw [show w_C5b4c1_1_0 = .reuse ((GGResIShape.C5b4c1.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c1.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c1.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c1_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C5b4c1_1_1) = true := by
  rw [show w_C5b4c1_1_1 = .reuse ((GGResIShape.C5b4c1.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c1.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c1.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c1_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C5b4c1_1_2) = true := by
  rw [show w_C5b4c1_1_2 = .norm [0, 1, 2, 3, 4] [0, 0, 2, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 1, 4, 3, 5, 4, 5, 3, 4, 1, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [0, 0, 2, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 1, 4, 3, 5, 4, 5, 3, 4, 1, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C5b4c1_1_2

theorem hcell_C5b4c1_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C5b4c1_2_0) = true := by
  rw [show w_C5b4c1_2_0 = .reuse ((GGResIShape.C5b4c1.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c1.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c1.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c1_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C5b4c1_2_1) = true := by
  rw [show w_C5b4c1_2_1 = .commonKernel [2, 1, 2, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 2, 0, 1, 1]) (by decide +kernel)

theorem hcell_C5b4c1_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C5b4c1_2_2) = true := by
  rw [show w_C5b4c1_2_2 = .reuse ((GGResIShape.C5b4c1.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c1.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c1.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_C5b4c1 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_C5b4c1_0_0), (0, 1, w_C5b4c1_0_1), (0, 2, w_C5b4c1_0_2), (1, 0, w_C5b4c1_1_0), (1, 1, w_C5b4c1_1_1), (1, 2, w_C5b4c1_1_2), (2, 0, w_C5b4c1_2_0), (2, 1, w_C5b4c1_2_1), (2, 2, w_C5b4c1_2_2)]

theorem hwits_C5b4c1 :
    GGResQTwoCellCheckAll (CartanMatrix.C 5) 4 1 (-1) (-1) wits_C5b4c1 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_0_0) (by rfl)]
      exact hcell_C5b4c1_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_0_1) (by rfl)]
      exact hcell_C5b4c1_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_0_2) (by rfl)]
      exact hcell_C5b4c1_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_1_0) (by rfl)]
      exact hcell_C5b4c1_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_1_1) (by rfl)]
      exact hcell_C5b4c1_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_1_2) (by rfl)]
      exact hcell_C5b4c1_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_2_0) (by rfl)]
      exact hcell_C5b4c1_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_2_1) (by rfl)]
      exact hcell_C5b4c1_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c1_2_2) (by rfl)]
      exact hcell_C5b4c1_2_2

@[expose] def w_C5b4c2_0_0 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 2, 0, 0, 0, 1] Rq2_2bc4de22acabb593 [5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5] 1

@[expose] def w_C5b4c2_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c2.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c2_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c2.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c2_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c2.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c2_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c2.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c2_1_2 : GGResQTwoCell 5 :=
  .commonKernel [0, 0, 0, 2, 1, 1]

@[expose] def w_C5b4c2_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c2.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c2_2_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 0, 1, 2, 1]

@[expose] def w_C5b4c2_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c2.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C5b4c2_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 5) 4 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 [1, 2, 0, 0, 0, 1] [5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC5) (by decide +kernel)
    (by decide +kernel) (pkListC5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C5b4c2_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C5b4c2_0_0) = true := by
  rw [show w_C5b4c2_0_0 = .norm [0, 1, 2, 3, 4] [1, 2, 0, 0, 0, 1] Rq2_2bc4de22acabb593 [5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 2, 0, 0, 0, 1] Rq2_2bc4de22acabb593 [5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C5b4c2_0_0

theorem hcell_C5b4c2_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C5b4c2_0_1) = true := by
  rw [show w_C5b4c2_0_1 = .reuse ((GGResIShape.C5b4c2.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c2.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c2.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c2_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C5b4c2_0_2) = true := by
  rw [show w_C5b4c2_0_2 = .reuse ((GGResIShape.C5b4c2.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c2.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c2.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c2_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C5b4c2_1_0) = true := by
  rw [show w_C5b4c2_1_0 = .reuse ((GGResIShape.C5b4c2.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c2.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c2.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c2_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C5b4c2_1_1) = true := by
  rw [show w_C5b4c2_1_1 = .reuse ((GGResIShape.C5b4c2.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c2.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c2.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c2_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C5b4c2_1_2) = true := by
  rw [show w_C5b4c2_1_2 = .commonKernel [0, 0, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 2, 1, 1]) (by decide +kernel)

theorem hcell_C5b4c2_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C5b4c2_2_0) = true := by
  rw [show w_C5b4c2_2_0 = .reuse ((GGResIShape.C5b4c2.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c2.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c2.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c2_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C5b4c2_2_1) = true := by
  rw [show w_C5b4c2_2_1 = .commonKernel [2, 1, 0, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 1, 2, 1]) (by decide +kernel)

theorem hcell_C5b4c2_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C5b4c2_2_2) = true := by
  rw [show w_C5b4c2_2_2 = .reuse ((GGResIShape.C5b4c2.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c2.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c2.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_C5b4c2 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_C5b4c2_0_0), (0, 1, w_C5b4c2_0_1), (0, 2, w_C5b4c2_0_2), (1, 0, w_C5b4c2_1_0), (1, 1, w_C5b4c2_1_1), (1, 2, w_C5b4c2_1_2), (2, 0, w_C5b4c2_2_0), (2, 1, w_C5b4c2_2_1), (2, 2, w_C5b4c2_2_2)]

theorem hwits_C5b4c2 :
    GGResQTwoCellCheckAll (CartanMatrix.C 5) 4 2 (-1) (-1) wits_C5b4c2 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_0_0) (by rfl)]
      exact hcell_C5b4c2_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_0_1) (by rfl)]
      exact hcell_C5b4c2_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_0_2) (by rfl)]
      exact hcell_C5b4c2_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_1_0) (by rfl)]
      exact hcell_C5b4c2_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_1_1) (by rfl)]
      exact hcell_C5b4c2_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_1_2) (by rfl)]
      exact hcell_C5b4c2_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_2_0) (by rfl)]
      exact hcell_C5b4c2_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_2_1) (by rfl)]
      exact hcell_C5b4c2_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c2_2_2) (by rfl)]
      exact hcell_C5b4c2_2_2

@[expose] def w_C5b4c3_0_0 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 1, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 5, 3, 4, 3, 5, 2, 3, 4, 1, 2, 3, 5] 0

@[expose] def w_C5b4c3_0_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 0, 2, 0, 1]

@[expose] def w_C5b4c3_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3_2_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 2, 0, 1, 1, 1]

@[expose] def w_C5b4c3_2_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 0, 2, 0, 1]

@[expose] def w_C5b4c3_2_2 : GGResQTwoCell 5 :=
  .commonKernel [0, 0, 0, 0, 2, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_C5b4c3_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 5) 4 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 [1, 2, 0, 1, 1, 1] [5, 3, 2, 1, 4, 3, 2, 5, 3, 4, 3, 5, 2, 3, 4, 1, 2, 3, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC5) (by decide +kernel)
    (by decide +kernel) (pkListC5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C5b4c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C5b4c3_0_0) = true := by
  rw [show w_C5b4c3_0_0 = .norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 1, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 5, 3, 4, 3, 5, 2, 3, 4, 1, 2, 3, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 1, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 5, 3, 4, 3, 5, 2, 3, 4, 1, 2, 3, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C5b4c3_0_0

theorem hcell_C5b4c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C5b4c3_0_1) = true := by
  rw [show w_C5b4c3_0_1 = .commonKernel [2, 1, 0, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 0, 1]) (by decide +kernel)

theorem hcell_C5b4c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C5b4c3_0_2) = true := by
  rw [show w_C5b4c3_0_2 = .reuse ((GGResIShape.C5b4c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C5b4c3_1_0) = true := by
  rw [show w_C5b4c3_1_0 = .reuse ((GGResIShape.C5b4c3.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c3.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C5b4c3_1_1) = true := by
  rw [show w_C5b4c3_1_1 = .reuse ((GGResIShape.C5b4c3.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c3.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C5b4c3_1_2) = true := by
  rw [show w_C5b4c3_1_2 = .reuse ((GGResIShape.C5b4c3.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c3.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C5b4c3_2_0) = true := by
  rw [show w_C5b4c3_2_0 = .commonKernel [1, 2, 0, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 1, 1, 1]) (by decide +kernel)

theorem hcell_C5b4c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C5b4c3_2_1) = true := by
  rw [show w_C5b4c3_2_1 = .commonKernel [2, 1, 0, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 0, 1]) (by decide +kernel)

theorem hcell_C5b4c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C5b4c3_2_2) = true := by
  rw [show w_C5b4c3_2_2 = .commonKernel [0, 0, 0, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_C5b4c3 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_C5b4c3_0_0), (0, 1, w_C5b4c3_0_1), (0, 2, w_C5b4c3_0_2), (1, 0, w_C5b4c3_1_0), (1, 1, w_C5b4c3_1_1), (1, 2, w_C5b4c3_1_2), (2, 0, w_C5b4c3_2_0), (2, 1, w_C5b4c3_2_1), (2, 2, w_C5b4c3_2_2)]

theorem hwits_C5b4c3 :
    GGResQTwoCellCheckAll (CartanMatrix.C 5) 4 3 (-1) (-1) wits_C5b4c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_0_0) (by rfl)]
      exact hcell_C5b4c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_0_1) (by rfl)]
      exact hcell_C5b4c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_0_2) (by rfl)]
      exact hcell_C5b4c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_1_0) (by rfl)]
      exact hcell_C5b4c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_1_1) (by rfl)]
      exact hcell_C5b4c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_1_2) (by rfl)]
      exact hcell_C5b4c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_2_0) (by rfl)]
      exact hcell_C5b4c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_2_1) (by rfl)]
      exact hcell_C5b4c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3_2_2) (by rfl)]
      exact hcell_C5b4c3_2_2

@[expose] def w_C5b4c3w12_0_0 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 0, 2, 2, 1]

@[expose] def w_C5b4c3w12_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w12_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w12_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w12_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w12_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w12_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w12_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w12_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 4, 3, 5, 3, 4, 2, 3, 4, 1, 2, 3, 5] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_C5b4c3w12_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 5) 4 3 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 [1, 2, 0, 1, 0, 1] [5, 3, 2, 1, 4, 3, 2, 4, 3, 5, 3, 4, 2, 3, 4, 1, 2, 3, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC5) (by decide +kernel)
    (by decide +kernel) (pkListC5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C5b4c3w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_C5b4c3w12_0_0) = true := by
  rw [show w_C5b4c3w12_0_0 = .commonKernel [2, 1, 0, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 2, 1]) (by decide +kernel)

theorem hcell_C5b4c3w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_C5b4c3w12_0_1) = true := by
  rw [show w_C5b4c3w12_0_1 = .reuse ((GGResIShape.C5b4c3w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c3w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_C5b4c3w12_0_2) = true := by
  rw [show w_C5b4c3w12_0_2 = .reuse ((GGResIShape.C5b4c3w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c3w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_C5b4c3w12_1_0) = true := by
  rw [show w_C5b4c3w12_1_0 = .reuse ((GGResIShape.C5b4c3w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c3w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_C5b4c3w12_1_1) = true := by
  rw [show w_C5b4c3w12_1_1 = .reuse ((GGResIShape.C5b4c3w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c3w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_C5b4c3w12_1_2) = true := by
  rw [show w_C5b4c3w12_1_2 = .reuse ((GGResIShape.C5b4c3w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c3w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_C5b4c3w12_2_0) = true := by
  rw [show w_C5b4c3w12_2_0 = .reuse ((GGResIShape.C5b4c3w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c3w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_C5b4c3w12_2_1) = true := by
  rw [show w_C5b4c3w12_2_1 = .reuse ((GGResIShape.C5b4c3w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c3w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_C5b4c3w12_2_2) = true := by
  rw [show w_C5b4c3w12_2_2 = .norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 4, 3, 5, 3, 4, 2, 3, 4, 1, 2, 3, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 0, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 4, 3, 5, 3, 4, 2, 3, 4, 1, 2, 3, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C5b4c3w12_2_2

@[expose] def wits_C5b4c3w12 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_C5b4c3w12_0_0), (0, 1, w_C5b4c3w12_0_1), (0, 2, w_C5b4c3w12_0_2), (1, 0, w_C5b4c3w12_1_0), (1, 1, w_C5b4c3w12_1_1), (1, 2, w_C5b4c3w12_1_2), (2, 0, w_C5b4c3w12_2_0), (2, 1, w_C5b4c3w12_2_1), (2, 2, w_C5b4c3w12_2_2)]

theorem hwits_C5b4c3w12 :
    GGResQTwoCellCheckAll (CartanMatrix.C 5) 4 3 (-1) (-2) wits_C5b4c3w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_0_0) (by rfl)]
      exact hcell_C5b4c3w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_0_1) (by rfl)]
      exact hcell_C5b4c3w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_0_2) (by rfl)]
      exact hcell_C5b4c3w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_1_0) (by rfl)]
      exact hcell_C5b4c3w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_1_1) (by rfl)]
      exact hcell_C5b4c3w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_1_2) (by rfl)]
      exact hcell_C5b4c3w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_2_0) (by rfl)]
      exact hcell_C5b4c3w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_2_1) (by rfl)]
      exact hcell_C5b4c3w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w12_2_2) (by rfl)]
      exact hcell_C5b4c3w12_2_2

@[expose] def w_C5b4c3w21_0_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 2, 0, 1, 1, 1]

@[expose] def w_C5b4c3w21_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w21_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w21_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w21_1_1 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [2, 1, 0, 2, 0, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 4, 3, 5, 3, 4, 2, 3, 4, 1, 2, 3, 5] 0

@[expose] def w_C5b4c3w21_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w21_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w21_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C5b4c3w21_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.C5b4c3w21.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C5b4c3w21_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 5) 4 3 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_2bc4de22acabb593 [2, 1, 0, 2, 0, 1] [5, 3, 2, 1, 4, 3, 2, 4, 3, 5, 3, 4, 2, 3, 4, 1, 2, 3, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC5) (by decide +kernel)
    (by decide +kernel) (pkListC5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C5b4c3w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C5b4c3w21_0_0) = true := by
  rw [show w_C5b4c3w21_0_0 = .commonKernel [1, 2, 0, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 1, 1, 1]) (by decide +kernel)

theorem hcell_C5b4c3w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C5b4c3w21_0_1) = true := by
  rw [show w_C5b4c3w21_0_1 = .reuse ((GGResIShape.C5b4c3w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c3w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C5b4c3w21_0_2) = true := by
  rw [show w_C5b4c3w21_0_2 = .reuse ((GGResIShape.C5b4c3w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c3w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C5b4c3w21_1_0) = true := by
  rw [show w_C5b4c3w21_1_0 = .reuse ((GGResIShape.C5b4c3w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c3w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C5b4c3w21_1_1) = true := by
  rw [show w_C5b4c3w21_1_1 = .norm [0, 1, 2, 3, 4] [2, 1, 0, 2, 0, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 4, 3, 5, 3, 4, 2, 3, 4, 1, 2, 3, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [2, 1, 0, 2, 0, 1] Rq2_2bc4de22acabb593 [5, 3, 2, 1, 4, 3, 2, 4, 3, 5, 3, 4, 2, 3, 4, 1, 2, 3, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C5b4c3w21_1_1

theorem hcell_C5b4c3w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C5b4c3w21_1_2) = true := by
  rw [show w_C5b4c3w21_1_2 = .reuse ((GGResIShape.C5b4c3w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c3w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C5b4c3w21_2_0) = true := by
  rw [show w_C5b4c3w21_2_0 = .reuse ((GGResIShape.C5b4c3w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C5b4c3w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C5b4c3w21_2_1) = true := by
  rw [show w_C5b4c3w21_2_1 = .reuse ((GGResIShape.C5b4c3w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C5b4c3w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C5b4c3w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 5) 4 3 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C5b4c3w21_2_2) = true := by
  rw [show w_C5b4c3w21_2_2 = .reuse ((GGResIShape.C5b4c3w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C5b4c3w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C5b4c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C5b4c3w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_C5b4c3w21 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_C5b4c3w21_0_0), (0, 1, w_C5b4c3w21_0_1), (0, 2, w_C5b4c3w21_0_2), (1, 0, w_C5b4c3w21_1_0), (1, 1, w_C5b4c3w21_1_1), (1, 2, w_C5b4c3w21_1_2), (2, 0, w_C5b4c3w21_2_0), (2, 1, w_C5b4c3w21_2_1), (2, 2, w_C5b4c3w21_2_2)]

theorem hwits_C5b4c3w21 :
    GGResQTwoCellCheckAll (CartanMatrix.C 5) 4 3 (-2) (-1) wits_C5b4c3w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_0_0) (by rfl)]
      exact hcell_C5b4c3w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_0_1) (by rfl)]
      exact hcell_C5b4c3w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_0_2) (by rfl)]
      exact hcell_C5b4c3w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_1_0) (by rfl)]
      exact hcell_C5b4c3w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_1_1) (by rfl)]
      exact hcell_C5b4c3w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_1_2) (by rfl)]
      exact hcell_C5b4c3w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_2_0) (by rfl)]
      exact hcell_C5b4c3w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_2_1) (by rfl)]
      exact hcell_C5b4c3w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C5b4c3w21_2_2) (by rfl)]
      exact hcell_C5b4c3w21_2_2

@[expose] def wits_C5_b0 (s : Fin 5 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 5) :=
  []

theorem cell_C5_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.C 5) 0 (GGResIDisp.C5.shapes_C5_b0) (wits_C5_b0) := by
  intro s hs
  simp [GGResIDisp.C5.shapes_C5_b0] at hs
theorem hsideOK_C5_b0 :
    ∀ s ∈ GGResIDisp.C5.shapes_C5_b0, ∀ w ∈ wits_C5_b0 s,
      ggResQTwoCellSideOK (0 : Fin 5) w.2.2 := by
  have hall : (GGResIDisp.C5.shapes_C5_b0.all fun s => (wits_C5_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 5) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_C5_b0 :
    ∀ s ∈ GGResIDisp.C5.shapes_C5_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.C5.shapes_C5_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def wits_C5_b4 (s : Fin 5 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 5) :=
  if s = (0, -1, -1) then wits_C5b4c0
  else if s = (0, -1, -2) then wits_C5b4c0w12
  else if s = (0, -2, -1) then wits_C5b4c0w21
  else if s = (1, -1, -1) then wits_C5b4c1
  else if s = (2, -1, -1) then wits_C5b4c2
  else if s = (3, -1, -1) then wits_C5b4c3
  else if s = (3, -1, -2) then wits_C5b4c3w12
  else if s = (3, -2, -1) then wits_C5b4c3w21
  else []

theorem cell_C5_b4 :
    GGResQTwoShapeCoverage (CartanMatrix.C 5) 4 (GGResIDisp.C5.shapes_C5_b4) (wits_C5_b4) := by
  intro s hs
  simp only [GGResIDisp.C5.shapes_C5_b4, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_C5_b4, if_pos rfl]
    exact hwits_C5b4c0
  · simp only [wits_C5_b4, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_C5b4c0w12
  · simp only [wits_C5_b4, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_C5b4c0w21
  · simp only [wits_C5_b4, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_C5b4c1
  · simp only [wits_C5_b4, if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_C5b4c2
  · simp only [wits_C5_b4, if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_C5b4c3
  · simp only [wits_C5_b4, if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_C5b4c3w12
  · simp only [wits_C5_b4, if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((3, -1, -2)))), if_pos rfl]
    exact hwits_C5b4c3w21
theorem hsideOK_C5_b4 :
    ∀ s ∈ GGResIDisp.C5.shapes_C5_b4, ∀ w ∈ wits_C5_b4 s,
      ggResQTwoCellSideOK (4 : Fin 5) w.2.2 := by
  have hall : (GGResIDisp.C5.shapes_C5_b4.all fun s => (wits_C5_b4 s).all fun w =>
      ggResQTwoCellSideOKB (4 : Fin 5) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_C5_b4 :
    ∀ s ∈ GGResIDisp.C5.shapes_C5_b4, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.C5.shapes_C5_b4.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataC5
