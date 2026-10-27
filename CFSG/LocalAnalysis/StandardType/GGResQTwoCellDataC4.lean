module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataC4

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_02ceec088d2778ce : List (Fin 5 × List (Fin 5)) :=
[(0, []), (1, []), (2, []), (3, []), (0, [1]), (1, [2]), (2, [3]), (3, [2]), (0, [2, 1]), (1, [3, 2]), (3, [1, 2]), (0, [3, 2, 1]), (1, [2, 3, 2]), (3, [0, 1, 2]), (0, [2, 3, 2, 1]), (0, [1, 2, 3, 2, 1])]

@[expose] def pkTabC4 : ℕ := 2426939914

@[expose] def pkDataC4 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 1074791682),
  (4, 4, 1075054597),
  (16, 16, 1344279553),
  (64, 64, 2156921857),
  (5, 5, 1075118600),
  (20, 20, 1409818645),
  (80, 144, 2685441025),
  (96, 80, 1080075265),
  (21, 21, 1426719784),
  (84, 148, 2829344917),
  (104, 84, 1074813097),
  (85, 149, 2862941288),
  (100, 164, 1080558757),
  (106, 85, 1074791510),
  (101, 165, 1080731992),
  (105, 169, 1074813441)]

theorem pkTabC4_spec : ∀ a b : Fin 4, ((CartanMatrix.C 4 a b : ℤ) : ZMod 3) =
    ((GGResQTwoPacked.pkLane pkTabC4 (a.val * 4 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedC4 : GGResQTwoPacked.pkSharedOK pkTabC4 4 ([0, 1, 2, 3] : List (Fin 5))
    Rq2_02ceec088d2778ce pkDataC4 = true := by
  decide +kernel

theorem pkListC4 (ib ic : Fin 4) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.C 4) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.C 4) ib ic e₁ e₂ u v k).get
      (Fin.last 5) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.C 4) ib ic e₁ e₂ u v)
        [0, 1, 2, 3] Rq2_02ceec088d2778ce ∧
      ∀ r ∈ Rq2_02ceec088d2778ce, ∃ d ∈ pkDataC4, GGResQTwoPacked.pkBlkM 4
        (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.C 4) ib ic e₁ e₂ u v) r) = d.2.2 :=
  GGResQTwoPacked.pkShared_sound pkSharedC4 (GGResQTwoPacked.pkTab_std pkTabC4_spec ib ic e₁ e₂ u v)
    h2 hx

@[expose] def w_C4b0c3_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 1, 0, 2, 1]

@[expose] def w_C4b0c3_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C4b0c3_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C4b0c3_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C4b0c3_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C4b0c3_1_2 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3

@[expose] def w_C4b0c3_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C4b0c3_2_1 : GGResQTwoCell 4 :=
  .commonKernel [1, 0, 2, 1, 1]

@[expose] def w_C4b0c3_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b0c3.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b0c3_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 0 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [0, 2, 1, 0, 1] [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C4b0c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C4b0c3_0_0) = true := by
  rw [show w_C4b0c3_0_0 = .commonKernel [2, 1, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 1]) (by decide +kernel)

theorem hcell_C4b0c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C4b0c3_0_1) = true := by
  rw [show w_C4b0c3_0_1 = .reuse ((GGResIShape.C4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b0c3.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b0c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C4b0c3_0_2) = true := by
  rw [show w_C4b0c3_0_2 = .reuse ((GGResIShape.C4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b0c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b0c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C4b0c3_1_0) = true := by
  rw [show w_C4b0c3_1_0 = .reuse ((GGResIShape.C4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b0c3.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b0c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C4b0c3_1_1) = true := by
  rw [show w_C4b0c3_1_1 = .reuse ((GGResIShape.C4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b0c3.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b0c3.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b0c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C4b0c3_1_2) = true := by
  rw [show w_C4b0c3_1_2 = .norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b0c3_1_2

theorem hcell_C4b0c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C4b0c3_2_0) = true := by
  rw [show w_C4b0c3_2_0 = .reuse ((GGResIShape.C4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b0c3.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b0c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C4b0c3_2_1) = true := by
  rw [show w_C4b0c3_2_1 = .commonKernel [1, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 0, 2, 1, 1]) (by decide +kernel)

theorem hcell_C4b0c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 0 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C4b0c3_2_2) = true := by
  rw [show w_C4b0c3_2_2 = .reuse ((GGResIShape.C4b0c3.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b0c3.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b0c3.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_C4b0c3 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_C4b0c3_0_0), (0, 1, w_C4b0c3_0_1), (0, 2, w_C4b0c3_0_2), (1, 0, w_C4b0c3_1_0), (1, 1, w_C4b0c3_1_1), (1, 2, w_C4b0c3_1_2), (2, 0, w_C4b0c3_2_0), (2, 1, w_C4b0c3_2_1), (2, 2, w_C4b0c3_2_2)]

theorem hwits_C4b0c3 :
    GGResQTwoCellCheckAll (CartanMatrix.C 4) 0 3 (-1) (-1) wits_C4b0c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_0_0) (by rfl)]
      exact hcell_C4b0c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_0_1) (by rfl)]
      exact hcell_C4b0c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_0_2) (by rfl)]
      exact hcell_C4b0c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_1_0) (by rfl)]
      exact hcell_C4b0c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_1_1) (by rfl)]
      exact hcell_C4b0c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_1_2) (by rfl)]
      exact hcell_C4b0c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_2_0) (by rfl)]
      exact hcell_C4b0c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_2_1) (by rfl)]
      exact hcell_C4b0c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b0c3_2_2) (by rfl)]
      exact hcell_C4b0c3_2_2

@[expose] def w_C4b3c0_0_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0_0_1 : GGResQTwoCell 4 :=
  .commonKernel [2, 0, 1, 2, 1]

@[expose] def w_C4b3c0_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0_1_2 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 4, 3, 4, 2, 3, 0, 4] 3

@[expose] def w_C4b3c0_2_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 1, 1, 1, 1]

@[expose] def w_C4b3c0_2_1 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [2, 0, 1, 2, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 4, 3, 4, 2, 3, 0, 4] 3

@[expose] def w_C4b3c0_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c0_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [0, 2, 1, 0, 1] [4, 0, 3, 2, 4, 3, 4, 2, 3, 0, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c0_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [2, 0, 1, 2, 1] [4, 0, 3, 2, 4, 3, 4, 2, 3, 0, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C4b3c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C4b3c0_0_0) = true := by
  rw [show w_C4b3c0_0_0 = .reuse ((GGResIShape.C4b3c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C4b3c0_0_1) = true := by
  rw [show w_C4b3c0_0_1 = .commonKernel [2, 0, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 1]) (by decide +kernel)

theorem hcell_C4b3c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C4b3c0_0_2) = true := by
  rw [show w_C4b3c0_0_2 = .reuse ((GGResIShape.C4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C4b3c0_1_0) = true := by
  rw [show w_C4b3c0_1_0 = .reuse ((GGResIShape.C4b3c0.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c0.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C4b3c0_1_1) = true := by
  rw [show w_C4b3c0_1_1 = .reuse ((GGResIShape.C4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c0.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C4b3c0_1_2) = true := by
  rw [show w_C4b3c0_1_2 = .norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 4, 3, 4, 2, 3, 0, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 4, 3, 4, 2, 3, 0, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c0_1_2

theorem hcell_C4b3c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C4b3c0_2_0) = true := by
  rw [show w_C4b3c0_2_0 = .commonKernel [1, 1, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 1]) (by decide +kernel)

theorem hcell_C4b3c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C4b3c0_2_1) = true := by
  rw [show w_C4b3c0_2_1 = .norm [0, 1, 2, 3] [2, 0, 1, 2, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 4, 3, 4, 2, 3, 0, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [2, 0, 1, 2, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 4, 3, 4, 2, 3, 0, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c0_2_1

theorem hcell_C4b3c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C4b3c0_2_2) = true := by
  rw [show w_C4b3c0_2_2 = .reuse ((GGResIShape.C4b3c0.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c0.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_C4b3c0 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_C4b3c0_0_0), (0, 1, w_C4b3c0_0_1), (0, 2, w_C4b3c0_0_2), (1, 0, w_C4b3c0_1_0), (1, 1, w_C4b3c0_1_1), (1, 2, w_C4b3c0_1_2), (2, 0, w_C4b3c0_2_0), (2, 1, w_C4b3c0_2_1), (2, 2, w_C4b3c0_2_2)]

theorem hwits_C4b3c0 :
    GGResQTwoCellCheckAll (CartanMatrix.C 4) 3 0 (-1) (-1) wits_C4b3c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_0_0) (by rfl)]
      exact hcell_C4b3c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_0_1) (by rfl)]
      exact hcell_C4b3c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_0_2) (by rfl)]
      exact hcell_C4b3c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_1_0) (by rfl)]
      exact hcell_C4b3c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_1_1) (by rfl)]
      exact hcell_C4b3c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_1_2) (by rfl)]
      exact hcell_C4b3c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_2_0) (by rfl)]
      exact hcell_C4b3c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_2_1) (by rfl)]
      exact hcell_C4b3c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0_2_2) (by rfl)]
      exact hcell_C4b3c0_2_2

@[expose] def w_C4b3c0w12_0_0 : GGResQTwoCell 4 :=
  .commonKernel [2, 2, 2, 2, 1]

@[expose] def w_C4b3c0w12_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w12_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w12_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w12_1_1 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [0, 1, 2, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3

@[expose] def w_C4b3c0w12_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w12_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w12_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w12_2_2 : GGResQTwoCell 4 :=
  .commonKernel [1, 0, 2, 1, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c0w12_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [0, 1, 2, 0, 1] [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C4b3c0w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_C4b3c0w12_0_0) = true := by
  rw [show w_C4b3c0w12_0_0 = .commonKernel [2, 2, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 2, 2, 2, 1]) (by decide +kernel)

theorem hcell_C4b3c0w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_C4b3c0w12_0_1) = true := by
  rw [show w_C4b3c0w12_0_1 = .reuse ((GGResIShape.C4b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_C4b3c0w12_0_2) = true := by
  rw [show w_C4b3c0w12_0_2 = .reuse ((GGResIShape.C4b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_C4b3c0w12_1_0) = true := by
  rw [show w_C4b3c0w12_1_0 = .reuse ((GGResIShape.C4b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_C4b3c0w12_1_1) = true := by
  rw [show w_C4b3c0w12_1_1 = .norm [0, 1, 2, 3] [0, 1, 2, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [0, 1, 2, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c0w12_1_1

theorem hcell_C4b3c0w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_C4b3c0w12_1_2) = true := by
  rw [show w_C4b3c0w12_1_2 = .reuse ((GGResIShape.C4b3c0w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c0w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_C4b3c0w12_2_0) = true := by
  rw [show w_C4b3c0w12_2_0 = .reuse ((GGResIShape.C4b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_C4b3c0w12_2_1) = true := by
  rw [show w_C4b3c0w12_2_1 = .reuse ((GGResIShape.C4b3c0w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c0w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_C4b3c0w12_2_2) = true := by
  rw [show w_C4b3c0w12_2_2 = .commonKernel [1, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 0, 2, 1, 1]) (by decide +kernel)

@[expose] def wits_C4b3c0w12 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_C4b3c0w12_0_0), (0, 1, w_C4b3c0w12_0_1), (0, 2, w_C4b3c0w12_0_2), (1, 0, w_C4b3c0w12_1_0), (1, 1, w_C4b3c0w12_1_1), (1, 2, w_C4b3c0w12_1_2), (2, 0, w_C4b3c0w12_2_0), (2, 1, w_C4b3c0w12_2_1), (2, 2, w_C4b3c0w12_2_2)]

theorem hwits_C4b3c0w12 :
    GGResQTwoCellCheckAll (CartanMatrix.C 4) 3 0 (-1) (-2) wits_C4b3c0w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_0_0) (by rfl)]
      exact hcell_C4b3c0w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_0_1) (by rfl)]
      exact hcell_C4b3c0w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_0_2) (by rfl)]
      exact hcell_C4b3c0w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_1_0) (by rfl)]
      exact hcell_C4b3c0w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_1_1) (by rfl)]
      exact hcell_C4b3c0w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_1_2) (by rfl)]
      exact hcell_C4b3c0w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_2_0) (by rfl)]
      exact hcell_C4b3c0w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_2_1) (by rfl)]
      exact hcell_C4b3c0w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w12_2_2) (by rfl)]
      exact hcell_C4b3c0w12_2_2

@[expose] def w_C4b3c0w21_0_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 1, 1, 1, 1]

@[expose] def w_C4b3c0w21_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w21_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w21_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w21_1_1 : GGResQTwoCell 4 :=
  .commonKernel [2, 0, 1, 2, 1]

@[expose] def w_C4b3c0w21_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w21_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w21_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c0w21_2_2 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c0w21_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [0, 2, 1, 0, 1] [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C4b3c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C4b3c0w21_0_0) = true := by
  rw [show w_C4b3c0w21_0_0 = .commonKernel [1, 1, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 1]) (by decide +kernel)

theorem hcell_C4b3c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C4b3c0w21_0_1) = true := by
  rw [show w_C4b3c0w21_0_1 = .reuse ((GGResIShape.C4b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C4b3c0w21_0_2) = true := by
  rw [show w_C4b3c0w21_0_2 = .reuse ((GGResIShape.C4b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C4b3c0w21_1_0) = true := by
  rw [show w_C4b3c0w21_1_0 = .reuse ((GGResIShape.C4b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C4b3c0w21_1_1) = true := by
  rw [show w_C4b3c0w21_1_1 = .commonKernel [2, 0, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 1]) (by decide +kernel)

theorem hcell_C4b3c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C4b3c0w21_1_2) = true := by
  rw [show w_C4b3c0w21_1_2 = .reuse ((GGResIShape.C4b3c0w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c0w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C4b3c0w21_2_0) = true := by
  rw [show w_C4b3c0w21_2_0 = .reuse ((GGResIShape.C4b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C4b3c0w21_2_1) = true := by
  rw [show w_C4b3c0w21_2_1 = .reuse ((GGResIShape.C4b3c0w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c0w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c0w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C4b3c0w21_2_2) = true := by
  rw [show w_C4b3c0w21_2_2 = .norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [0, 2, 1, 0, 1] Rq2_02ceec088d2778ce [4, 0, 3, 2, 3, 4, 3, 2, 3, 0, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c0w21_2_2

@[expose] def wits_C4b3c0w21 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_C4b3c0w21_0_0), (0, 1, w_C4b3c0w21_0_1), (0, 2, w_C4b3c0w21_0_2), (1, 0, w_C4b3c0w21_1_0), (1, 1, w_C4b3c0w21_1_1), (1, 2, w_C4b3c0w21_1_2), (2, 0, w_C4b3c0w21_2_0), (2, 1, w_C4b3c0w21_2_1), (2, 2, w_C4b3c0w21_2_2)]

theorem hwits_C4b3c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.C 4) 3 0 (-2) (-1) wits_C4b3c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_0_0) (by rfl)]
      exact hcell_C4b3c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_0_1) (by rfl)]
      exact hcell_C4b3c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_0_2) (by rfl)]
      exact hcell_C4b3c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_1_0) (by rfl)]
      exact hcell_C4b3c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_1_1) (by rfl)]
      exact hcell_C4b3c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_1_2) (by rfl)]
      exact hcell_C4b3c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_2_0) (by rfl)]
      exact hcell_C4b3c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_2_1) (by rfl)]
      exact hcell_C4b3c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c0w21_2_2) (by rfl)]
      exact hcell_C4b3c0w21_2_2

@[expose] def w_C4b3c1_0_0 : GGResQTwoCell 4 :=
  .commonKernel [1, 2, 2, 2, 1]

@[expose] def w_C4b3c1_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c1.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c1_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c1.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c1_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c1.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c1_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c1.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c1_1_2 : GGResQTwoCell 4 :=
  .commonKernel [0, 0, 2, 1, 1]

@[expose] def w_C4b3c1_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c1.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c1_2_1 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [2, 1, 2, 0, 1] Rq2_02ceec088d2778ce [4, 1, 0, 2, 1, 4, 3, 4, 1, 2, 0, 1, 4] 3

@[expose] def w_C4b3c1_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c1.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c1_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 1 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [2, 1, 2, 0, 1] [4, 1, 0, 2, 1, 4, 3, 4, 1, 2, 0, 1, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C4b3c1_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C4b3c1_0_0) = true := by
  rw [show w_C4b3c1_0_0 = .commonKernel [1, 2, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 2, 2, 1]) (by decide +kernel)

theorem hcell_C4b3c1_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C4b3c1_0_1) = true := by
  rw [show w_C4b3c1_0_1 = .reuse ((GGResIShape.C4b3c1.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c1.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c1.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c1_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C4b3c1_0_2) = true := by
  rw [show w_C4b3c1_0_2 = .reuse ((GGResIShape.C4b3c1.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c1.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c1.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c1_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C4b3c1_1_0) = true := by
  rw [show w_C4b3c1_1_0 = .reuse ((GGResIShape.C4b3c1.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c1.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c1.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c1_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C4b3c1_1_1) = true := by
  rw [show w_C4b3c1_1_1 = .reuse ((GGResIShape.C4b3c1.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c1.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c1.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c1_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C4b3c1_1_2) = true := by
  rw [show w_C4b3c1_1_2 = .commonKernel [0, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 2, 1, 1]) (by decide +kernel)

theorem hcell_C4b3c1_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C4b3c1_2_0) = true := by
  rw [show w_C4b3c1_2_0 = .reuse ((GGResIShape.C4b3c1.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c1.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c1.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c1_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C4b3c1_2_1) = true := by
  rw [show w_C4b3c1_2_1 = .norm [0, 1, 2, 3] [2, 1, 2, 0, 1] Rq2_02ceec088d2778ce [4, 1, 0, 2, 1, 4, 3, 4, 1, 2, 0, 1, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [2, 1, 2, 0, 1] Rq2_02ceec088d2778ce [4, 1, 0, 2, 1, 4, 3, 4, 1, 2, 0, 1, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c1_2_1

theorem hcell_C4b3c1_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C4b3c1_2_2) = true := by
  rw [show w_C4b3c1_2_2 = .reuse ((GGResIShape.C4b3c1.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c1.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c1.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_C4b3c1 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_C4b3c1_0_0), (0, 1, w_C4b3c1_0_1), (0, 2, w_C4b3c1_0_2), (1, 0, w_C4b3c1_1_0), (1, 1, w_C4b3c1_1_1), (1, 2, w_C4b3c1_1_2), (2, 0, w_C4b3c1_2_0), (2, 1, w_C4b3c1_2_1), (2, 2, w_C4b3c1_2_2)]

theorem hwits_C4b3c1 :
    GGResQTwoCellCheckAll (CartanMatrix.C 4) 3 1 (-1) (-1) wits_C4b3c1 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_0_0) (by rfl)]
      exact hcell_C4b3c1_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_0_1) (by rfl)]
      exact hcell_C4b3c1_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_0_2) (by rfl)]
      exact hcell_C4b3c1_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_1_0) (by rfl)]
      exact hcell_C4b3c1_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_1_1) (by rfl)]
      exact hcell_C4b3c1_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_1_2) (by rfl)]
      exact hcell_C4b3c1_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_2_0) (by rfl)]
      exact hcell_C4b3c1_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_2_1) (by rfl)]
      exact hcell_C4b3c1_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c1_2_2) (by rfl)]
      exact hcell_C4b3c1_2_2

@[expose] def w_C4b3c2_0_0 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [1, 2, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 4, 2, 3, 2, 4, 1, 2, 3, 0, 1, 2, 4] 3

@[expose] def w_C4b3c2_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2_2_1 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [2, 1, 0, 1, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 4, 2, 3, 2, 4, 1, 2, 3, 0, 1, 2, 4] 3

@[expose] def w_C4b3c2_2_2 : GGResQTwoCell 4 :=
  .commonKernel [0, 0, 0, 2, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c2_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [1, 2, 0, 0, 1] [4, 2, 1, 0, 3, 2, 1, 4, 2, 3, 2, 4, 1, 2, 3, 0, 1, 2, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c2_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [2, 1, 0, 1, 1] [4, 2, 1, 0, 3, 2, 1, 4, 2, 3, 2, 4, 1, 2, 3, 0, 1, 2, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C4b3c2_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C4b3c2_0_0) = true := by
  rw [show w_C4b3c2_0_0 = .norm [0, 1, 2, 3] [1, 2, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 4, 2, 3, 2, 4, 1, 2, 3, 0, 1, 2, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [1, 2, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 4, 2, 3, 2, 4, 1, 2, 3, 0, 1, 2, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c2_0_0

theorem hcell_C4b3c2_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C4b3c2_0_1) = true := by
  rw [show w_C4b3c2_0_1 = .reuse ((GGResIShape.C4b3c2.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c2.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C4b3c2_0_2) = true := by
  rw [show w_C4b3c2_0_2 = .reuse ((GGResIShape.C4b3c2.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c2.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C4b3c2_1_0) = true := by
  rw [show w_C4b3c2_1_0 = .reuse ((GGResIShape.C4b3c2.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c2.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C4b3c2_1_1) = true := by
  rw [show w_C4b3c2_1_1 = .reuse ((GGResIShape.C4b3c2.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c2.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C4b3c2_1_2) = true := by
  rw [show w_C4b3c2_1_2 = .reuse ((GGResIShape.C4b3c2.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c2.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C4b3c2_2_0) = true := by
  rw [show w_C4b3c2_2_0 = .reuse ((GGResIShape.C4b3c2.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c2.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C4b3c2_2_1) = true := by
  rw [show w_C4b3c2_2_1 = .norm [0, 1, 2, 3] [2, 1, 0, 1, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 4, 2, 3, 2, 4, 1, 2, 3, 0, 1, 2, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [2, 1, 0, 1, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 4, 2, 3, 2, 4, 1, 2, 3, 0, 1, 2, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c2_2_1

theorem hcell_C4b3c2_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C4b3c2_2_2) = true := by
  rw [show w_C4b3c2_2_2 = .commonKernel [0, 0, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_C4b3c2 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_C4b3c2_0_0), (0, 1, w_C4b3c2_0_1), (0, 2, w_C4b3c2_0_2), (1, 0, w_C4b3c2_1_0), (1, 1, w_C4b3c2_1_1), (1, 2, w_C4b3c2_1_2), (2, 0, w_C4b3c2_2_0), (2, 1, w_C4b3c2_2_1), (2, 2, w_C4b3c2_2_2)]

theorem hwits_C4b3c2 :
    GGResQTwoCellCheckAll (CartanMatrix.C 4) 3 2 (-1) (-1) wits_C4b3c2 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_0_0) (by rfl)]
      exact hcell_C4b3c2_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_0_1) (by rfl)]
      exact hcell_C4b3c2_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_0_2) (by rfl)]
      exact hcell_C4b3c2_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_1_0) (by rfl)]
      exact hcell_C4b3c2_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_1_1) (by rfl)]
      exact hcell_C4b3c2_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_1_2) (by rfl)]
      exact hcell_C4b3c2_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_2_0) (by rfl)]
      exact hcell_C4b3c2_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_2_1) (by rfl)]
      exact hcell_C4b3c2_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2_2_2) (by rfl)]
      exact hcell_C4b3c2_2_2

@[expose] def w_C4b3c2w12_0_0 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [2, 1, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 3, 2, 4, 2, 3, 1, 2, 3, 0, 1, 2, 4] 3

@[expose] def w_C4b3c2w12_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w12_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w12_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w12_1_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w12_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w12_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w12_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w12.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w12_2_2 : GGResQTwoCell 4 :=
  .commonKernel [1, 2, 0, 2, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c2w12_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 2 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [2, 1, 0, 0, 1] [4, 2, 1, 0, 3, 2, 1, 3, 2, 4, 2, 3, 1, 2, 3, 0, 1, 2, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C4b3c2w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_C4b3c2w12_0_0) = true := by
  rw [show w_C4b3c2w12_0_0 = .norm [0, 1, 2, 3] [2, 1, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 3, 2, 4, 2, 3, 1, 2, 3, 0, 1, 2, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [2, 1, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 3, 2, 4, 2, 3, 1, 2, 3, 0, 1, 2, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c2w12_0_0

theorem hcell_C4b3c2w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_C4b3c2w12_0_1) = true := by
  rw [show w_C4b3c2w12_0_1 = .reuse ((GGResIShape.C4b3c2w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c2w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_C4b3c2w12_0_2) = true := by
  rw [show w_C4b3c2w12_0_2 = .reuse ((GGResIShape.C4b3c2w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c2w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_C4b3c2w12_1_0) = true := by
  rw [show w_C4b3c2w12_1_0 = .reuse ((GGResIShape.C4b3c2w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c2w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_C4b3c2w12_1_1) = true := by
  rw [show w_C4b3c2w12_1_1 = .reuse ((GGResIShape.C4b3c2w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c2w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_C4b3c2w12_1_2) = true := by
  rw [show w_C4b3c2w12_1_2 = .reuse ((GGResIShape.C4b3c2w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c2w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_C4b3c2w12_2_0) = true := by
  rw [show w_C4b3c2w12_2_0 = .reuse ((GGResIShape.C4b3c2w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c2w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_C4b3c2w12_2_1) = true := by
  rw [show w_C4b3c2w12_2_1 = .reuse ((GGResIShape.C4b3c2w12.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w12.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c2w12.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_C4b3c2w12_2_2) = true := by
  rw [show w_C4b3c2w12_2_2 = .commonKernel [1, 2, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_C4b3c2w12 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_C4b3c2w12_0_0), (0, 1, w_C4b3c2w12_0_1), (0, 2, w_C4b3c2w12_0_2), (1, 0, w_C4b3c2w12_1_0), (1, 1, w_C4b3c2w12_1_1), (1, 2, w_C4b3c2w12_1_2), (2, 0, w_C4b3c2w12_2_0), (2, 1, w_C4b3c2w12_2_1), (2, 2, w_C4b3c2w12_2_2)]

theorem hwits_C4b3c2w12 :
    GGResQTwoCellCheckAll (CartanMatrix.C 4) 3 2 (-1) (-2) wits_C4b3c2w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_0_0) (by rfl)]
      exact hcell_C4b3c2w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_0_1) (by rfl)]
      exact hcell_C4b3c2w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_0_2) (by rfl)]
      exact hcell_C4b3c2w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_1_0) (by rfl)]
      exact hcell_C4b3c2w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_1_1) (by rfl)]
      exact hcell_C4b3c2w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_1_2) (by rfl)]
      exact hcell_C4b3c2w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_2_0) (by rfl)]
      exact hcell_C4b3c2w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_2_1) (by rfl)]
      exact hcell_C4b3c2w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w12_2_2) (by rfl)]
      exact hcell_C4b3c2w12_2_2

@[expose] def w_C4b3c2w21_0_0 : GGResQTwoCell 4 :=
  .norm [0, 1, 2, 3] [1, 2, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 3, 2, 4, 2, 3, 1, 2, 3, 0, 1, 2, 4] 3

@[expose] def w_C4b3c2w21_0_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w21_0_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w21_1_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w21_1_1 : GGResQTwoCell 4 :=
  .commonKernel [2, 1, 0, 1, 1]

@[expose] def w_C4b3c2w21_1_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w21.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w21_2_0 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w21_2_1 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_C4b3c2w21_2_2 : GGResQTwoCell 4 :=
  .reuse ((GGResIShape.C4b3c2w21.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_C4b3c2w21_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.C 4) 3 2 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3] Rq2_02ceec088d2778ce [1, 2, 0, 0, 1] [4, 2, 1, 0, 3, 2, 1, 3, 2, 4, 2, 3, 1, 2, 3, 0, 1, 2, 4] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataC4) (by decide +kernel)
    (by decide +kernel) (pkListC4 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_C4b3c2w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_C4b3c2w21_0_0) = true := by
  rw [show w_C4b3c2w21_0_0 = .norm [0, 1, 2, 3] [1, 2, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 3, 2, 4, 2, 3, 1, 2, 3, 0, 1, 2, 4] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3] [1, 2, 0, 0, 1] Rq2_02ceec088d2778ce [4, 2, 1, 0, 3, 2, 1, 3, 2, 4, 2, 3, 1, 2, 3, 0, 1, 2, 4] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_C4b3c2w21_0_0

theorem hcell_C4b3c2w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_C4b3c2w21_0_1) = true := by
  rw [show w_C4b3c2w21_0_1 = .reuse ((GGResIShape.C4b3c2w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c2w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_C4b3c2w21_0_2) = true := by
  rw [show w_C4b3c2w21_0_2 = .reuse ((GGResIShape.C4b3c2w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c2w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_C4b3c2w21_1_0) = true := by
  rw [show w_C4b3c2w21_1_0 = .reuse ((GGResIShape.C4b3c2w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c2w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_C4b3c2w21_1_1) = true := by
  rw [show w_C4b3c2w21_1_1 = .commonKernel [2, 1, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 1, 1]) (by decide +kernel)

theorem hcell_C4b3c2w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_C4b3c2w21_1_2) = true := by
  rw [show w_C4b3c2w21_1_2 = .reuse ((GGResIShape.C4b3c2w21.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w21.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c2w21.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_C4b3c2w21_2_0) = true := by
  rw [show w_C4b3c2w21_2_0 = .reuse ((GGResIShape.C4b3c2w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.C4b3c2w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_C4b3c2w21_2_1) = true := by
  rw [show w_C4b3c2w21_2_1 = .reuse ((GGResIShape.C4b3c2w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.C4b3c2w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_C4b3c2w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.C 4) 3 2 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_C4b3c2w21_2_2) = true := by
  rw [show w_C4b3c2w21_2_2 = .reuse ((GGResIShape.C4b3c2w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.C4b3c2w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.C4b3c2w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.C4b3c2w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_C4b3c2w21 : List (ℕ × ℕ × GGResQTwoCell 4) :=
  [(0, 0, w_C4b3c2w21_0_0), (0, 1, w_C4b3c2w21_0_1), (0, 2, w_C4b3c2w21_0_2), (1, 0, w_C4b3c2w21_1_0), (1, 1, w_C4b3c2w21_1_1), (1, 2, w_C4b3c2w21_1_2), (2, 0, w_C4b3c2w21_2_0), (2, 1, w_C4b3c2w21_2_1), (2, 2, w_C4b3c2w21_2_2)]

theorem hwits_C4b3c2w21 :
    GGResQTwoCellCheckAll (CartanMatrix.C 4) 3 2 (-2) (-1) wits_C4b3c2w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_0_0) (by rfl)]
      exact hcell_C4b3c2w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_0_1) (by rfl)]
      exact hcell_C4b3c2w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_0_2) (by rfl)]
      exact hcell_C4b3c2w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_1_0) (by rfl)]
      exact hcell_C4b3c2w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_1_1) (by rfl)]
      exact hcell_C4b3c2w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_1_2) (by rfl)]
      exact hcell_C4b3c2w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_2_0) (by rfl)]
      exact hcell_C4b3c2w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_2_1) (by rfl)]
      exact hcell_C4b3c2w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_C4b3c2w21_2_2) (by rfl)]
      exact hcell_C4b3c2w21_2_2

@[expose] def wits_C4_b0 (s : Fin 4 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 4) :=
  if s = (3, -1, -1) then wits_C4b0c3
  else []

theorem cell_C4_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.C 4) 0 (GGResIDisp.C4.shapes_C4_b0) (wits_C4_b0) := by
  intro s hs
  simp only [GGResIDisp.C4.shapes_C4_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · simp only [wits_C4_b0, if_pos rfl]
    exact hwits_C4b0c3
theorem hsideOK_C4_b0 :
    ∀ s ∈ GGResIDisp.C4.shapes_C4_b0, ∀ w ∈ wits_C4_b0 s,
      ggResQTwoCellSideOK (0 : Fin 4) w.2.2 := by
  have hall : (GGResIDisp.C4.shapes_C4_b0.all fun s => (wits_C4_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 4) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_C4_b0 :
    ∀ s ∈ GGResIDisp.C4.shapes_C4_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.C4.shapes_C4_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def wits_C4_b3 (s : Fin 4 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 4) :=
  if s = (0, -1, -1) then wits_C4b3c0
  else if s = (0, -1, -2) then wits_C4b3c0w12
  else if s = (0, -2, -1) then wits_C4b3c0w21
  else if s = (1, -1, -1) then wits_C4b3c1
  else if s = (2, -1, -1) then wits_C4b3c2
  else if s = (2, -1, -2) then wits_C4b3c2w12
  else if s = (2, -2, -1) then wits_C4b3c2w21
  else []

theorem cell_C4_b3 :
    GGResQTwoShapeCoverage (CartanMatrix.C 4) 3 (GGResIDisp.C4.shapes_C4_b3) (wits_C4_b3) := by
  intro s hs
  simp only [GGResIDisp.C4.shapes_C4_b3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_C4_b3, if_pos rfl]
    exact hwits_C4b3c0
  · simp only [wits_C4_b3, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_C4b3c0w12
  · simp only [wits_C4_b3, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_C4b3c0w21
  · simp only [wits_C4_b3, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_C4b3c1
  · simp only [wits_C4_b3, if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_C4b3c2
  · simp only [wits_C4_b3, if_neg (by decide : ¬ (((2, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -1, -2)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -2)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_C4b3c2w12
  · simp only [wits_C4_b3, if_neg (by decide : ¬ (((2, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((2, -2, -1)) = ((2, -1, -2)))), if_pos rfl]
    exact hwits_C4b3c2w21
theorem hsideOK_C4_b3 :
    ∀ s ∈ GGResIDisp.C4.shapes_C4_b3, ∀ w ∈ wits_C4_b3 s,
      ggResQTwoCellSideOK (3 : Fin 4) w.2.2 := by
  have hall : (GGResIDisp.C4.shapes_C4_b3.all fun s => (wits_C4_b3 s).all fun w =>
      ggResQTwoCellSideOKB (3 : Fin 4) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_C4_b3 :
    ∀ s ∈ GGResIDisp.C4.shapes_C4_b3, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.C4.shapes_C4_b3.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataC4
