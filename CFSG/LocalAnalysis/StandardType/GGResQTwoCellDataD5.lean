module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataD5

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_18423184c7c41865 : List (Fin 6 × List (Fin 6)) :=
[(0, []), (1, []), (2, []), (3, []), (4, []), (0, [1]), (1, [2]), (2, [3]), (2, [4]), (0, [2, 1]), (1, [3, 2]), (1, [4, 2]), (2, [4, 3]), (0, [3, 2, 1]), (0, [4, 2, 1]), (1, [4, 3, 2]), (0, [4, 3, 2, 1]), (1, [2, 4, 3, 2]), (0, [2, 4, 3, 2, 1]), (0, [1, 2, 4, 3, 2, 1])]

@[expose] def pkTabD5 : ℕ := 598306837276682

@[expose] def pkDataD5 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 281543712969730),
  (4, 4, 281543717167109),
  (16, 16, 299153095675905),
  (64, 64, 281612499554305),
  (256, 256, 563018958114817),
  (5, 5, 281543718209544),
  (20, 20, 303555412000789),
  (80, 80, 369470400974849),
  (272, 272, 35545686495233),
  (21, 21, 304655999438888),
  (84, 84, 373876920057941),
  (276, 276, 44345554665749),
  (336, 336, 176505993121793),
  (85, 85, 374978579009704),
  (277, 277, 46545651110440),
  (340, 340, 185311032934741),
  (341, 341, 187512204038824),
  (356, 356, 281544409223525),
  (357, 357, 281544411686552),
  (361, 361, 281543713646593)]

theorem pkTabD5_spec : ∀ a b : Fin 5, ((CartanMatrix.D 5 a b : ℤ) : ZMod 3) =
    ((GGResQTwoPacked.pkLane pkTabD5 (a.val * 5 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedD5 : GGResQTwoPacked.pkSharedOK pkTabD5 5 ([0, 1, 2, 3, 4] : List (Fin 6))
    Rq2_18423184c7c41865 pkDataD5 = true := by
  decide +kernel

theorem pkListD5 (ib ic : Fin 5) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.D 5) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.D 5) ib ic e₁ e₂ u v k).get
      (Fin.last 6) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.D 5) ib ic e₁ e₂ u v)
        [0, 1, 2, 3, 4] Rq2_18423184c7c41865 ∧
      ∀ r ∈ Rq2_18423184c7c41865, ∃ d ∈ pkDataD5, GGResQTwoPacked.pkBlkM 5
        (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.D 5) ib ic e₁ e₂ u v) r) = d.2.2 :=
  GGResQTwoPacked.pkShared_sound pkSharedD5 (GGResQTwoPacked.pkTab_std pkTabD5_spec ib ic e₁ e₂ u v)
    h2 hx

@[expose] def w_D5b0c3_0_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c3.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c3_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c3_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c3_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c3_1_1 : GGResQTwoCell 5 :=
  .commonKernel [1, 0, 2, 0, 1, 1]

@[expose] def w_D5b0c3_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c3.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c3_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c3_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c3.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c3_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [0, 2, 1, 1, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 0, 5] 1

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b0c3_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 0 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [0, 2, 1, 1, 2, 1] [5, 0, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b0c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b0c3_0_0) = true := by
  rw [show w_D5b0c3_0_0 = .reuse ((GGResIShape.D5b0c3.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c3.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b0c3.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b0c3_0_1) = true := by
  rw [show w_D5b0c3_0_1 = .reuse ((GGResIShape.D5b0c3.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c3.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b0c3_0_2) = true := by
  rw [show w_D5b0c3_0_2 = .reuse ((GGResIShape.D5b0c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b0c3_1_0) = true := by
  rw [show w_D5b0c3_1_0 = .reuse ((GGResIShape.D5b0c3.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c3.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b0c3_1_1) = true := by
  rw [show w_D5b0c3_1_1 = .commonKernel [1, 0, 2, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 0, 2, 0, 1, 1]) (by decide +kernel)

theorem hcell_D5b0c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b0c3_1_2) = true := by
  rw [show w_D5b0c3_1_2 = .reuse ((GGResIShape.D5b0c3.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c3.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b0c3.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b0c3_2_0) = true := by
  rw [show w_D5b0c3_2_0 = .reuse ((GGResIShape.D5b0c3.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c3.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b0c3_2_1) = true := by
  rw [show w_D5b0c3_2_1 = .reuse ((GGResIShape.D5b0c3.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c3.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b0c3.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b0c3_2_2) = true := by
  rw [show w_D5b0c3_2_2 = .norm [0, 1, 2, 3, 4] [0, 2, 1, 1, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [0, 2, 1, 1, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b0c3_2_2

@[expose] def wits_D5b0c3 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b0c3_0_0), (0, 1, w_D5b0c3_0_1), (0, 2, w_D5b0c3_0_2), (1, 0, w_D5b0c3_1_0), (1, 1, w_D5b0c3_1_1), (1, 2, w_D5b0c3_1_2), (2, 0, w_D5b0c3_2_0), (2, 1, w_D5b0c3_2_1), (2, 2, w_D5b0c3_2_2)]

theorem hwits_D5b0c3 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 0 3 (-1) (-1) wits_D5b0c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_0_0) (by rfl)]
      exact hcell_D5b0c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_0_1) (by rfl)]
      exact hcell_D5b0c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_0_2) (by rfl)]
      exact hcell_D5b0c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_1_0) (by rfl)]
      exact hcell_D5b0c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_1_1) (by rfl)]
      exact hcell_D5b0c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_1_2) (by rfl)]
      exact hcell_D5b0c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_2_0) (by rfl)]
      exact hcell_D5b0c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_2_1) (by rfl)]
      exact hcell_D5b0c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c3_2_2) (by rfl)]
      exact hcell_D5b0c3_2_2

@[expose] def w_D5b0c4_0_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c4.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c4_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c4.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c4_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c4.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c4_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c4.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c4_1_1 : GGResQTwoCell 5 :=
  .commonKernel [1, 0, 2, 1, 0, 1]

@[expose] def w_D5b0c4_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c4.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c4_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c4.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c4_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b0c4.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D5b0c4_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [0, 2, 1, 2, 1, 1] Rq2_18423184c7c41865 [5, 0, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 0, 5] 1

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b0c4_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 0 4 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [0, 2, 1, 2, 1, 1] [5, 0, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b0c4_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b0c4_0_0) = true := by
  rw [show w_D5b0c4_0_0 = .reuse ((GGResIShape.D5b0c4.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c4.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b0c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b0c4.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c4_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b0c4_0_1) = true := by
  rw [show w_D5b0c4_0_1 = .reuse ((GGResIShape.D5b0c4.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c4.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b0c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b0c4.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c4_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b0c4_0_2) = true := by
  rw [show w_D5b0c4_0_2 = .reuse ((GGResIShape.D5b0c4.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c4.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b0c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b0c4.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c4_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b0c4_1_0) = true := by
  rw [show w_D5b0c4_1_0 = .reuse ((GGResIShape.D5b0c4.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c4.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b0c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b0c4.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c4_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b0c4_1_1) = true := by
  rw [show w_D5b0c4_1_1 = .commonKernel [1, 0, 2, 1, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 0, 2, 1, 0, 1]) (by decide +kernel)

theorem hcell_D5b0c4_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b0c4_1_2) = true := by
  rw [show w_D5b0c4_1_2 = .reuse ((GGResIShape.D5b0c4.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c4.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b0c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b0c4.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c4_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b0c4_2_0) = true := by
  rw [show w_D5b0c4_2_0 = .reuse ((GGResIShape.D5b0c4.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c4.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b0c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b0c4.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c4_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b0c4_2_1) = true := by
  rw [show w_D5b0c4_2_1 = .reuse ((GGResIShape.D5b0c4.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b0c4.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b0c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b0c4.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b0c4_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 0 4 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b0c4_2_2) = true := by
  rw [show w_D5b0c4_2_2 = .norm [0, 1, 2, 3, 4] [0, 2, 1, 2, 1, 1] Rq2_18423184c7c41865 [5, 0, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [0, 2, 1, 2, 1, 1] Rq2_18423184c7c41865 [5, 0, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b0c4_2_2

@[expose] def wits_D5b0c4 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b0c4_0_0), (0, 1, w_D5b0c4_0_1), (0, 2, w_D5b0c4_0_2), (1, 0, w_D5b0c4_1_0), (1, 1, w_D5b0c4_1_1), (1, 2, w_D5b0c4_1_2), (2, 0, w_D5b0c4_2_0), (2, 1, w_D5b0c4_2_1), (2, 2, w_D5b0c4_2_2)]

theorem hwits_D5b0c4 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 0 4 (-1) (-1) wits_D5b0c4 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_0_0) (by rfl)]
      exact hcell_D5b0c4_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_0_1) (by rfl)]
      exact hcell_D5b0c4_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_0_2) (by rfl)]
      exact hcell_D5b0c4_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_1_0) (by rfl)]
      exact hcell_D5b0c4_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_1_1) (by rfl)]
      exact hcell_D5b0c4_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_1_2) (by rfl)]
      exact hcell_D5b0c4_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_2_0) (by rfl)]
      exact hcell_D5b0c4_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_2_1) (by rfl)]
      exact hcell_D5b0c4_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b0c4_2_2) (by rfl)]
      exact hcell_D5b0c4_2_2

@[expose] def w_D5b3c0_0_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0_1_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 1, 1, 2, 2, 1]

@[expose] def w_D5b3c0_1_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 0, 1, 0, 2, 1]

@[expose] def w_D5b3c0_1_2 : GGResQTwoCell 5 :=
  .commonKernel [0, 2, 1, 1, 2, 1]

@[expose] def w_D5b3c0_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0_2_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 0, 1, 0, 2, 1]

@[expose] def w_D5b3c0_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [0, 2, 1, 1, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 0, 5] 1

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b3c0_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 3 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [0, 2, 1, 1, 2, 1] [5, 0, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b3c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b3c0_0_0) = true := by
  rw [show w_D5b3c0_0_0 = .reuse ((GGResIShape.D5b3c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b3c0_0_1) = true := by
  rw [show w_D5b3c0_0_1 = .reuse ((GGResIShape.D5b3c0.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c0.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b3c0_0_2) = true := by
  rw [show w_D5b3c0_0_2 = .reuse ((GGResIShape.D5b3c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b3c0_1_0) = true := by
  rw [show w_D5b3c0_1_0 = .commonKernel [1, 1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D5b3c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b3c0_1_1) = true := by
  rw [show w_D5b3c0_1_1 = .commonKernel [2, 0, 1, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 0, 2, 1]) (by decide +kernel)

theorem hcell_D5b3c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b3c0_1_2) = true := by
  rw [show w_D5b3c0_1_2 = .commonKernel [0, 2, 1, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 1, 1, 2, 1]) (by decide +kernel)

theorem hcell_D5b3c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b3c0_2_0) = true := by
  rw [show w_D5b3c0_2_0 = .reuse ((GGResIShape.D5b3c0.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c0.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b3c0_2_1) = true := by
  rw [show w_D5b3c0_2_1 = .commonKernel [2, 0, 1, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 0, 2, 1]) (by decide +kernel)

theorem hcell_D5b3c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b3c0_2_2) = true := by
  rw [show w_D5b3c0_2_2 = .norm [0, 1, 2, 3, 4] [0, 2, 1, 1, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [0, 2, 1, 1, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b3c0_2_2

@[expose] def wits_D5b3c0 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b3c0_0_0), (0, 1, w_D5b3c0_0_1), (0, 2, w_D5b3c0_0_2), (1, 0, w_D5b3c0_1_0), (1, 1, w_D5b3c0_1_1), (1, 2, w_D5b3c0_1_2), (2, 0, w_D5b3c0_2_0), (2, 1, w_D5b3c0_2_1), (2, 2, w_D5b3c0_2_2)]

theorem hwits_D5b3c0 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 3 0 (-1) (-1) wits_D5b3c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_0_0) (by rfl)]
      exact hcell_D5b3c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_0_1) (by rfl)]
      exact hcell_D5b3c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_0_2) (by rfl)]
      exact hcell_D5b3c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_1_0) (by rfl)]
      exact hcell_D5b3c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_1_1) (by rfl)]
      exact hcell_D5b3c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_1_2) (by rfl)]
      exact hcell_D5b3c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_2_0) (by rfl)]
      exact hcell_D5b3c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_2_1) (by rfl)]
      exact hcell_D5b3c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0_2_2) (by rfl)]
      exact hcell_D5b3c0_2_2

@[expose] def w_D5b3c0w12_0_0 : GGResQTwoCell 5 :=
  .commonKernel [2, 2, 2, 1, 1, 1]

@[expose] def w_D5b3c0w12_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w12_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w12_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w12_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w12_1_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 0, 2, 0, 1, 1] Rq2_18423184c7c41865 [5, 0, 3, 5, 3, 0, 5] 1

@[expose] def w_D5b3c0w12_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w12_2_1 : GGResQTwoCell 5 :=
  .commonKernel [0, 1, 2, 2, 1, 1]

@[expose] def w_D5b3c0w12_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w12.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b3c0w12_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 3 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [1, 0, 2, 0, 1, 1] [5, 0, 3, 5, 3, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b3c0w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D5b3c0w12_0_0) = true := by
  rw [show w_D5b3c0w12_0_0 = .commonKernel [2, 2, 2, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 2, 2, 1, 1, 1]) (by decide +kernel)

theorem hcell_D5b3c0w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D5b3c0w12_0_1) = true := by
  rw [show w_D5b3c0w12_0_1 = .reuse ((GGResIShape.D5b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D5b3c0w12_0_2) = true := by
  rw [show w_D5b3c0w12_0_2 = .reuse ((GGResIShape.D5b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D5b3c0w12_1_0) = true := by
  rw [show w_D5b3c0w12_1_0 = .reuse ((GGResIShape.D5b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D5b3c0w12_1_1) = true := by
  rw [show w_D5b3c0w12_1_1 = .reuse ((GGResIShape.D5b3c0w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D5b3c0w12_1_2) = true := by
  rw [show w_D5b3c0w12_1_2 = .norm [0, 1, 2, 3, 4] [1, 0, 2, 0, 1, 1] Rq2_18423184c7c41865 [5, 0, 3, 5, 3, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 0, 2, 0, 1, 1] Rq2_18423184c7c41865 [5, 0, 3, 5, 3, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b3c0w12_1_2

theorem hcell_D5b3c0w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D5b3c0w12_2_0) = true := by
  rw [show w_D5b3c0w12_2_0 = .reuse ((GGResIShape.D5b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D5b3c0w12_2_1) = true := by
  rw [show w_D5b3c0w12_2_1 = .commonKernel [0, 1, 2, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 1, 2, 2, 1, 1]) (by decide +kernel)

theorem hcell_D5b3c0w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D5b3c0w12_2_2) = true := by
  rw [show w_D5b3c0w12_2_2 = .reuse ((GGResIShape.D5b3c0w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c0w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D5b3c0w12 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b3c0w12_0_0), (0, 1, w_D5b3c0w12_0_1), (0, 2, w_D5b3c0w12_0_2), (1, 0, w_D5b3c0w12_1_0), (1, 1, w_D5b3c0w12_1_1), (1, 2, w_D5b3c0w12_1_2), (2, 0, w_D5b3c0w12_2_0), (2, 1, w_D5b3c0w12_2_1), (2, 2, w_D5b3c0w12_2_2)]

theorem hwits_D5b3c0w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 3 0 (-1) (-2) wits_D5b3c0w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_0_0) (by rfl)]
      exact hcell_D5b3c0w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_0_1) (by rfl)]
      exact hcell_D5b3c0w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_0_2) (by rfl)]
      exact hcell_D5b3c0w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_1_0) (by rfl)]
      exact hcell_D5b3c0w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_1_1) (by rfl)]
      exact hcell_D5b3c0w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_1_2) (by rfl)]
      exact hcell_D5b3c0w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_2_0) (by rfl)]
      exact hcell_D5b3c0w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_2_1) (by rfl)]
      exact hcell_D5b3c0w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w12_2_2) (by rfl)]
      exact hcell_D5b3c0w12_2_2

@[expose] def w_D5b3c0w21_0_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 1, 1, 2, 2, 1]

@[expose] def w_D5b3c0w21_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w21_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w21_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w21_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w21_1_2 : GGResQTwoCell 5 :=
  .commonKernel [0, 2, 1, 1, 2, 1]

@[expose] def w_D5b3c0w21_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c0w21_2_1 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [2, 0, 1, 0, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 5, 3, 0, 5] 1

@[expose] def w_D5b3c0w21_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b3c0w21_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 3 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [2, 0, 1, 0, 2, 1] [5, 0, 3, 5, 3, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b3c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b3c0w21_0_0) = true := by
  rw [show w_D5b3c0w21_0_0 = .commonKernel [1, 1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D5b3c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b3c0w21_0_1) = true := by
  rw [show w_D5b3c0w21_0_1 = .reuse ((GGResIShape.D5b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b3c0w21_0_2) = true := by
  rw [show w_D5b3c0w21_0_2 = .reuse ((GGResIShape.D5b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b3c0w21_1_0) = true := by
  rw [show w_D5b3c0w21_1_0 = .reuse ((GGResIShape.D5b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b3c0w21_1_1) = true := by
  rw [show w_D5b3c0w21_1_1 = .reuse ((GGResIShape.D5b3c0w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c0w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b3c0w21_1_2) = true := by
  rw [show w_D5b3c0w21_1_2 = .commonKernel [0, 2, 1, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 1, 1, 2, 1]) (by decide +kernel)

theorem hcell_D5b3c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b3c0w21_2_0) = true := by
  rw [show w_D5b3c0w21_2_0 = .reuse ((GGResIShape.D5b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b3c0w21_2_1) = true := by
  rw [show w_D5b3c0w21_2_1 = .norm [0, 1, 2, 3, 4] [2, 0, 1, 0, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 5, 3, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [2, 0, 1, 0, 2, 1] Rq2_18423184c7c41865 [5, 0, 3, 5, 3, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b3c0w21_2_1

theorem hcell_D5b3c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b3c0w21_2_2) = true := by
  rw [show w_D5b3c0w21_2_2 = .reuse ((GGResIShape.D5b3c0w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c0w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D5b3c0w21 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b3c0w21_0_0), (0, 1, w_D5b3c0w21_0_1), (0, 2, w_D5b3c0w21_0_2), (1, 0, w_D5b3c0w21_1_0), (1, 1, w_D5b3c0w21_1_1), (1, 2, w_D5b3c0w21_1_2), (2, 0, w_D5b3c0w21_2_0), (2, 1, w_D5b3c0w21_2_1), (2, 2, w_D5b3c0w21_2_2)]

theorem hwits_D5b3c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 3 0 (-2) (-1) wits_D5b3c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_0_0) (by rfl)]
      exact hcell_D5b3c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_0_1) (by rfl)]
      exact hcell_D5b3c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_0_2) (by rfl)]
      exact hcell_D5b3c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_1_0) (by rfl)]
      exact hcell_D5b3c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_1_1) (by rfl)]
      exact hcell_D5b3c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_1_2) (by rfl)]
      exact hcell_D5b3c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_2_0) (by rfl)]
      exact hcell_D5b3c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_2_1) (by rfl)]
      exact hcell_D5b3c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c0w21_2_2) (by rfl)]
      exact hcell_D5b3c0w21_2_2

@[expose] def w_D5b3c1_0_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 2, 2, 1, 1, 1]

@[expose] def w_D5b3c1_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c1.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c1_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c1.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c1_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c1.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c1_1_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 2, 2, 1, 1]

@[expose] def w_D5b3c1_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c1.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c1_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c1.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c1_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c1.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c1_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [0, 0, 2, 0, 1, 1] Rq2_18423184c7c41865 [5, 1, 0, 2, 1, 3, 5, 3, 1, 2, 0, 1, 5] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b3c1_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 3 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [0, 0, 2, 0, 1, 1] [5, 1, 0, 2, 1, 3, 5, 3, 1, 2, 0, 1, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b3c1_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b3c1_0_0) = true := by
  rw [show w_D5b3c1_0_0 = .commonKernel [1, 2, 2, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 2, 1, 1, 1]) (by decide +kernel)

theorem hcell_D5b3c1_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b3c1_0_1) = true := by
  rw [show w_D5b3c1_0_1 = .reuse ((GGResIShape.D5b3c1.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c1.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c1.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c1_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b3c1_0_2) = true := by
  rw [show w_D5b3c1_0_2 = .reuse ((GGResIShape.D5b3c1.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c1.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c1.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c1_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b3c1_1_0) = true := by
  rw [show w_D5b3c1_1_0 = .reuse ((GGResIShape.D5b3c1.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c1.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c1.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c1_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b3c1_1_1) = true := by
  rw [show w_D5b3c1_1_1 = .commonKernel [2, 1, 2, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 2, 2, 1, 1]) (by decide +kernel)

theorem hcell_D5b3c1_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b3c1_1_2) = true := by
  rw [show w_D5b3c1_1_2 = .reuse ((GGResIShape.D5b3c1.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c1.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c1.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c1_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b3c1_2_0) = true := by
  rw [show w_D5b3c1_2_0 = .reuse ((GGResIShape.D5b3c1.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c1.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c1.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c1_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b3c1_2_1) = true := by
  rw [show w_D5b3c1_2_1 = .reuse ((GGResIShape.D5b3c1.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c1.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c1.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c1_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b3c1_2_2) = true := by
  rw [show w_D5b3c1_2_2 = .norm [0, 1, 2, 3, 4] [0, 0, 2, 0, 1, 1] Rq2_18423184c7c41865 [5, 1, 0, 2, 1, 3, 5, 3, 1, 2, 0, 1, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [0, 0, 2, 0, 1, 1] Rq2_18423184c7c41865 [5, 1, 0, 2, 1, 3, 5, 3, 1, 2, 0, 1, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b3c1_2_2

@[expose] def wits_D5b3c1 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b3c1_0_0), (0, 1, w_D5b3c1_0_1), (0, 2, w_D5b3c1_0_2), (1, 0, w_D5b3c1_1_0), (1, 1, w_D5b3c1_1_1), (1, 2, w_D5b3c1_1_2), (2, 0, w_D5b3c1_2_0), (2, 1, w_D5b3c1_2_1), (2, 2, w_D5b3c1_2_2)]

theorem hwits_D5b3c1 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 3 1 (-1) (-1) wits_D5b3c1 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_0_0) (by rfl)]
      exact hcell_D5b3c1_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_0_1) (by rfl)]
      exact hcell_D5b3c1_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_0_2) (by rfl)]
      exact hcell_D5b3c1_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_1_0) (by rfl)]
      exact hcell_D5b3c1_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_1_1) (by rfl)]
      exact hcell_D5b3c1_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_1_2) (by rfl)]
      exact hcell_D5b3c1_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_2_0) (by rfl)]
      exact hcell_D5b3c1_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_2_1) (by rfl)]
      exact hcell_D5b3c1_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c1_2_2) (by rfl)]
      exact hcell_D5b3c1_2_2

@[expose] def w_D5b3c4_0_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 2, 0, 2, 2, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 5, 4, 3, 5, 2, 3, 1, 2, 4, 5] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b3c4_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 3 4 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [1, 2, 0, 2, 2, 1] [5, 3, 2, 1, 4, 2, 5, 4, 3, 5, 2, 3, 1, 2, 4, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b3c4_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b3c4_0_0) = true := by
  rw [show w_D5b3c4_0_0 = .reuse ((GGResIShape.D5b3c4.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c4.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b3c4_0_1) = true := by
  rw [show w_D5b3c4_0_1 = .reuse ((GGResIShape.D5b3c4.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c4.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b3c4_0_2) = true := by
  rw [show w_D5b3c4_0_2 = .reuse ((GGResIShape.D5b3c4.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c4.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b3c4_1_0) = true := by
  rw [show w_D5b3c4_1_0 = .reuse ((GGResIShape.D5b3c4.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c4.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b3c4_1_1) = true := by
  rw [show w_D5b3c4_1_1 = .reuse ((GGResIShape.D5b3c4.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c4.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b3c4_1_2) = true := by
  rw [show w_D5b3c4_1_2 = .reuse ((GGResIShape.D5b3c4.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c4.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b3c4_2_0) = true := by
  rw [show w_D5b3c4_2_0 = .reuse ((GGResIShape.D5b3c4.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c4.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b3c4_2_1) = true := by
  rw [show w_D5b3c4_2_1 = .reuse ((GGResIShape.D5b3c4.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c4.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b3c4_2_2) = true := by
  rw [show w_D5b3c4_2_2 = .norm [0, 1, 2, 3, 4] [1, 2, 0, 2, 2, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 5, 4, 3, 5, 2, 3, 1, 2, 4, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 2, 0, 2, 2, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 5, 4, 3, 5, 2, 3, 1, 2, 4, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b3c4_2_2

@[expose] def wits_D5b3c4 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b3c4_0_0), (0, 1, w_D5b3c4_0_1), (0, 2, w_D5b3c4_0_2), (1, 0, w_D5b3c4_1_0), (1, 1, w_D5b3c4_1_1), (1, 2, w_D5b3c4_1_2), (2, 0, w_D5b3c4_2_0), (2, 1, w_D5b3c4_2_1), (2, 2, w_D5b3c4_2_2)]

theorem hwits_D5b3c4 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 3 4 (-1) (-1) wits_D5b3c4 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_0_0) (by rfl)]
      exact hcell_D5b3c4_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_0_1) (by rfl)]
      exact hcell_D5b3c4_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_0_2) (by rfl)]
      exact hcell_D5b3c4_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_1_0) (by rfl)]
      exact hcell_D5b3c4_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_1_1) (by rfl)]
      exact hcell_D5b3c4_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_1_2) (by rfl)]
      exact hcell_D5b3c4_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_2_0) (by rfl)]
      exact hcell_D5b3c4_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_2_1) (by rfl)]
      exact hcell_D5b3c4_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4_2_2) (by rfl)]
      exact hcell_D5b3c4_2_2

@[expose] def w_D5b3c4w12_0_0 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 2, 0, 0, 1, 1] Rq2_18423184c7c41865 [5, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 5] 0

@[expose] def w_D5b3c4w12_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w12_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w12_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w12_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w12_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w12_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w12_2_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 0, 1, 1, 1]

@[expose] def w_D5b3c4w12_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w12.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b3c4w12_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 3 4 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [1, 2, 0, 0, 1, 1] [5, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b3c4w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D5b3c4w12_0_0) = true := by
  rw [show w_D5b3c4w12_0_0 = .norm [0, 1, 2, 3, 4] [1, 2, 0, 0, 1, 1] Rq2_18423184c7c41865 [5, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 2, 0, 0, 1, 1] Rq2_18423184c7c41865 [5, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b3c4w12_0_0

theorem hcell_D5b3c4w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D5b3c4w12_0_1) = true := by
  rw [show w_D5b3c4w12_0_1 = .reuse ((GGResIShape.D5b3c4w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c4w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D5b3c4w12_0_2) = true := by
  rw [show w_D5b3c4w12_0_2 = .reuse ((GGResIShape.D5b3c4w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c4w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D5b3c4w12_1_0) = true := by
  rw [show w_D5b3c4w12_1_0 = .reuse ((GGResIShape.D5b3c4w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c4w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D5b3c4w12_1_1) = true := by
  rw [show w_D5b3c4w12_1_1 = .reuse ((GGResIShape.D5b3c4w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c4w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D5b3c4w12_1_2) = true := by
  rw [show w_D5b3c4w12_1_2 = .reuse ((GGResIShape.D5b3c4w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c4w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D5b3c4w12_2_0) = true := by
  rw [show w_D5b3c4w12_2_0 = .reuse ((GGResIShape.D5b3c4w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c4w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D5b3c4w12_2_1) = true := by
  rw [show w_D5b3c4w12_2_1 = .commonKernel [2, 1, 0, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 1, 1, 1]) (by decide +kernel)

theorem hcell_D5b3c4w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D5b3c4w12_2_2) = true := by
  rw [show w_D5b3c4w12_2_2 = .reuse ((GGResIShape.D5b3c4w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c4w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D5b3c4w12 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b3c4w12_0_0), (0, 1, w_D5b3c4w12_0_1), (0, 2, w_D5b3c4w12_0_2), (1, 0, w_D5b3c4w12_1_0), (1, 1, w_D5b3c4w12_1_1), (1, 2, w_D5b3c4w12_1_2), (2, 0, w_D5b3c4w12_2_0), (2, 1, w_D5b3c4w12_2_1), (2, 2, w_D5b3c4w12_2_2)]

theorem hwits_D5b3c4w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 3 4 (-1) (-2) wits_D5b3c4w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_0_0) (by rfl)]
      exact hcell_D5b3c4w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_0_1) (by rfl)]
      exact hcell_D5b3c4w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_0_2) (by rfl)]
      exact hcell_D5b3c4w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_1_0) (by rfl)]
      exact hcell_D5b3c4w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_1_1) (by rfl)]
      exact hcell_D5b3c4w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_1_2) (by rfl)]
      exact hcell_D5b3c4w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_2_0) (by rfl)]
      exact hcell_D5b3c4w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_2_1) (by rfl)]
      exact hcell_D5b3c4w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w12_2_2) (by rfl)]
      exact hcell_D5b3c4w12_2_2

@[expose] def w_D5b3c4w21_0_0 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [2, 1, 0, 0, 2, 1] Rq2_18423184c7c41865 [5, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 5] 0

@[expose] def w_D5b3c4w21_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w21_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w21_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w21_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w21_1_2 : GGResQTwoCell 5 :=
  .commonKernel [1, 2, 0, 2, 2, 1]

@[expose] def w_D5b3c4w21_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w21_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D5b3c4w21_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b3c4w21.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b3c4w21_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 3 4 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [2, 1, 0, 0, 2, 1] [5, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b3c4w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b3c4w21_0_0) = true := by
  rw [show w_D5b3c4w21_0_0 = .norm [0, 1, 2, 3, 4] [2, 1, 0, 0, 2, 1] Rq2_18423184c7c41865 [5, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [2, 1, 0, 0, 2, 1] Rq2_18423184c7c41865 [5, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b3c4w21_0_0

theorem hcell_D5b3c4w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b3c4w21_0_1) = true := by
  rw [show w_D5b3c4w21_0_1 = .reuse ((GGResIShape.D5b3c4w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c4w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b3c4w21_0_2) = true := by
  rw [show w_D5b3c4w21_0_2 = .reuse ((GGResIShape.D5b3c4w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c4w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b3c4w21_1_0) = true := by
  rw [show w_D5b3c4w21_1_0 = .reuse ((GGResIShape.D5b3c4w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c4w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b3c4w21_1_1) = true := by
  rw [show w_D5b3c4w21_1_1 = .reuse ((GGResIShape.D5b3c4w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c4w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b3c4w21_1_2) = true := by
  rw [show w_D5b3c4w21_1_2 = .commonKernel [1, 2, 0, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 2, 2, 1]) (by decide +kernel)

theorem hcell_D5b3c4w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b3c4w21_2_0) = true := by
  rw [show w_D5b3c4w21_2_0 = .reuse ((GGResIShape.D5b3c4w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b3c4w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b3c4w21_2_1) = true := by
  rw [show w_D5b3c4w21_2_1 = .reuse ((GGResIShape.D5b3c4w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b3c4w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b3c4w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 3 4 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b3c4w21_2_2) = true := by
  rw [show w_D5b3c4w21_2_2 = .reuse ((GGResIShape.D5b3c4w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b3c4w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b3c4w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b3c4w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D5b3c4w21 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b3c4w21_0_0), (0, 1, w_D5b3c4w21_0_1), (0, 2, w_D5b3c4w21_0_2), (1, 0, w_D5b3c4w21_1_0), (1, 1, w_D5b3c4w21_1_1), (1, 2, w_D5b3c4w21_1_2), (2, 0, w_D5b3c4w21_2_0), (2, 1, w_D5b3c4w21_2_1), (2, 2, w_D5b3c4w21_2_2)]

theorem hwits_D5b3c4w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 3 4 (-2) (-1) wits_D5b3c4w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_0_0) (by rfl)]
      exact hcell_D5b3c4w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_0_1) (by rfl)]
      exact hcell_D5b3c4w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_0_2) (by rfl)]
      exact hcell_D5b3c4w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_1_0) (by rfl)]
      exact hcell_D5b3c4w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_1_1) (by rfl)]
      exact hcell_D5b3c4w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_1_2) (by rfl)]
      exact hcell_D5b3c4w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_2_0) (by rfl)]
      exact hcell_D5b3c4w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_2_1) (by rfl)]
      exact hcell_D5b3c4w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b3c4w21_2_2) (by rfl)]
      exact hcell_D5b3c4w21_2_2

@[expose] def w_D5b4c0_0_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0_1_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 1, 1, 2, 2, 1]

@[expose] def w_D5b4c0_1_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 0, 1, 2, 0, 1]

@[expose] def w_D5b4c0_1_2 : GGResQTwoCell 5 :=
  .commonKernel [0, 2, 1, 2, 1, 1]

@[expose] def w_D5b4c0_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0_2_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 0, 1, 2, 0, 1]

@[expose] def w_D5b4c0_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [0, 2, 1, 2, 1, 1] Rq2_18423184c7c41865 [5, 0, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 0, 5] 1

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b4c0_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 4 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [0, 2, 1, 2, 1, 1] [5, 0, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b4c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b4c0_0_0) = true := by
  rw [show w_D5b4c0_0_0 = .reuse ((GGResIShape.D5b4c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b4c0_0_1) = true := by
  rw [show w_D5b4c0_0_1 = .reuse ((GGResIShape.D5b4c0.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c0.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b4c0_0_2) = true := by
  rw [show w_D5b4c0_0_2 = .reuse ((GGResIShape.D5b4c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b4c0_1_0) = true := by
  rw [show w_D5b4c0_1_0 = .commonKernel [1, 1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D5b4c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b4c0_1_1) = true := by
  rw [show w_D5b4c0_1_1 = .commonKernel [2, 0, 1, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 0, 1]) (by decide +kernel)

theorem hcell_D5b4c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b4c0_1_2) = true := by
  rw [show w_D5b4c0_1_2 = .commonKernel [0, 2, 1, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 1, 2, 1, 1]) (by decide +kernel)

theorem hcell_D5b4c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b4c0_2_0) = true := by
  rw [show w_D5b4c0_2_0 = .reuse ((GGResIShape.D5b4c0.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c0.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b4c0_2_1) = true := by
  rw [show w_D5b4c0_2_1 = .commonKernel [2, 0, 1, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 0, 1]) (by decide +kernel)

theorem hcell_D5b4c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b4c0_2_2) = true := by
  rw [show w_D5b4c0_2_2 = .norm [0, 1, 2, 3, 4] [0, 2, 1, 2, 1, 1] Rq2_18423184c7c41865 [5, 0, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [0, 2, 1, 2, 1, 1] Rq2_18423184c7c41865 [5, 0, 4, 2, 1, 3, 2, 4, 5, 4, 2, 3, 1, 2, 4, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b4c0_2_2

@[expose] def wits_D5b4c0 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b4c0_0_0), (0, 1, w_D5b4c0_0_1), (0, 2, w_D5b4c0_0_2), (1, 0, w_D5b4c0_1_0), (1, 1, w_D5b4c0_1_1), (1, 2, w_D5b4c0_1_2), (2, 0, w_D5b4c0_2_0), (2, 1, w_D5b4c0_2_1), (2, 2, w_D5b4c0_2_2)]

theorem hwits_D5b4c0 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 4 0 (-1) (-1) wits_D5b4c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_0_0) (by rfl)]
      exact hcell_D5b4c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_0_1) (by rfl)]
      exact hcell_D5b4c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_0_2) (by rfl)]
      exact hcell_D5b4c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_1_0) (by rfl)]
      exact hcell_D5b4c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_1_1) (by rfl)]
      exact hcell_D5b4c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_1_2) (by rfl)]
      exact hcell_D5b4c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_2_0) (by rfl)]
      exact hcell_D5b4c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_2_1) (by rfl)]
      exact hcell_D5b4c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0_2_2) (by rfl)]
      exact hcell_D5b4c0_2_2

@[expose] def w_D5b4c0w12_0_0 : GGResQTwoCell 5 :=
  .commonKernel [2, 2, 2, 1, 1, 1]

@[expose] def w_D5b4c0w12_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w12_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w12_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w12_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w12_1_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 0, 2, 1, 0, 1] Rq2_18423184c7c41865 [5, 0, 4, 5, 4, 0, 5] 1

@[expose] def w_D5b4c0w12_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w12_2_1 : GGResQTwoCell 5 :=
  .commonKernel [0, 1, 2, 1, 2, 1]

@[expose] def w_D5b4c0w12_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w12.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b4c0w12_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 4 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [1, 0, 2, 1, 0, 1] [5, 0, 4, 5, 4, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b4c0w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D5b4c0w12_0_0) = true := by
  rw [show w_D5b4c0w12_0_0 = .commonKernel [2, 2, 2, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 2, 2, 1, 1, 1]) (by decide +kernel)

theorem hcell_D5b4c0w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D5b4c0w12_0_1) = true := by
  rw [show w_D5b4c0w12_0_1 = .reuse ((GGResIShape.D5b4c0w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D5b4c0w12_0_2) = true := by
  rw [show w_D5b4c0w12_0_2 = .reuse ((GGResIShape.D5b4c0w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D5b4c0w12_1_0) = true := by
  rw [show w_D5b4c0w12_1_0 = .reuse ((GGResIShape.D5b4c0w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D5b4c0w12_1_1) = true := by
  rw [show w_D5b4c0w12_1_1 = .reuse ((GGResIShape.D5b4c0w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c0w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D5b4c0w12_1_2) = true := by
  rw [show w_D5b4c0w12_1_2 = .norm [0, 1, 2, 3, 4] [1, 0, 2, 1, 0, 1] Rq2_18423184c7c41865 [5, 0, 4, 5, 4, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 0, 2, 1, 0, 1] Rq2_18423184c7c41865 [5, 0, 4, 5, 4, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b4c0w12_1_2

theorem hcell_D5b4c0w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D5b4c0w12_2_0) = true := by
  rw [show w_D5b4c0w12_2_0 = .reuse ((GGResIShape.D5b4c0w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c0w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D5b4c0w12_2_1) = true := by
  rw [show w_D5b4c0w12_2_1 = .commonKernel [0, 1, 2, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 1, 2, 1, 2, 1]) (by decide +kernel)

theorem hcell_D5b4c0w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D5b4c0w12_2_2) = true := by
  rw [show w_D5b4c0w12_2_2 = .reuse ((GGResIShape.D5b4c0w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c0w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D5b4c0w12 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b4c0w12_0_0), (0, 1, w_D5b4c0w12_0_1), (0, 2, w_D5b4c0w12_0_2), (1, 0, w_D5b4c0w12_1_0), (1, 1, w_D5b4c0w12_1_1), (1, 2, w_D5b4c0w12_1_2), (2, 0, w_D5b4c0w12_2_0), (2, 1, w_D5b4c0w12_2_1), (2, 2, w_D5b4c0w12_2_2)]

theorem hwits_D5b4c0w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 4 0 (-1) (-2) wits_D5b4c0w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_0_0) (by rfl)]
      exact hcell_D5b4c0w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_0_1) (by rfl)]
      exact hcell_D5b4c0w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_0_2) (by rfl)]
      exact hcell_D5b4c0w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_1_0) (by rfl)]
      exact hcell_D5b4c0w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_1_1) (by rfl)]
      exact hcell_D5b4c0w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_1_2) (by rfl)]
      exact hcell_D5b4c0w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_2_0) (by rfl)]
      exact hcell_D5b4c0w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_2_1) (by rfl)]
      exact hcell_D5b4c0w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w12_2_2) (by rfl)]
      exact hcell_D5b4c0w12_2_2

@[expose] def w_D5b4c0w21_0_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 1, 1, 2, 2, 1]

@[expose] def w_D5b4c0w21_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w21_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w21_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w21_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w21_1_2 : GGResQTwoCell 5 :=
  .commonKernel [0, 2, 1, 2, 1, 1]

@[expose] def w_D5b4c0w21_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c0w21_2_1 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [2, 0, 1, 2, 0, 1] Rq2_18423184c7c41865 [5, 0, 4, 5, 4, 0, 5] 1

@[expose] def w_D5b4c0w21_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b4c0w21_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 4 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [2, 0, 1, 2, 0, 1] [5, 0, 4, 5, 4, 0, 5] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b4c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b4c0w21_0_0) = true := by
  rw [show w_D5b4c0w21_0_0 = .commonKernel [1, 1, 1, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 2, 2, 1]) (by decide +kernel)

theorem hcell_D5b4c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b4c0w21_0_1) = true := by
  rw [show w_D5b4c0w21_0_1 = .reuse ((GGResIShape.D5b4c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b4c0w21_0_2) = true := by
  rw [show w_D5b4c0w21_0_2 = .reuse ((GGResIShape.D5b4c0w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c0w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b4c0w21_1_0) = true := by
  rw [show w_D5b4c0w21_1_0 = .reuse ((GGResIShape.D5b4c0w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c0w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b4c0w21_1_1) = true := by
  rw [show w_D5b4c0w21_1_1 = .reuse ((GGResIShape.D5b4c0w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c0w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b4c0w21_1_2) = true := by
  rw [show w_D5b4c0w21_1_2 = .commonKernel [0, 2, 1, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 2, 1, 2, 1, 1]) (by decide +kernel)

theorem hcell_D5b4c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b4c0w21_2_0) = true := by
  rw [show w_D5b4c0w21_2_0 = .reuse ((GGResIShape.D5b4c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b4c0w21_2_1) = true := by
  rw [show w_D5b4c0w21_2_1 = .norm [0, 1, 2, 3, 4] [2, 0, 1, 2, 0, 1] Rq2_18423184c7c41865 [5, 0, 4, 5, 4, 0, 5] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [2, 0, 1, 2, 0, 1] Rq2_18423184c7c41865 [5, 0, 4, 5, 4, 0, 5] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b4c0w21_2_1

theorem hcell_D5b4c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b4c0w21_2_2) = true := by
  rw [show w_D5b4c0w21_2_2 = .reuse ((GGResIShape.D5b4c0w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c0w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c0w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D5b4c0w21 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b4c0w21_0_0), (0, 1, w_D5b4c0w21_0_1), (0, 2, w_D5b4c0w21_0_2), (1, 0, w_D5b4c0w21_1_0), (1, 1, w_D5b4c0w21_1_1), (1, 2, w_D5b4c0w21_1_2), (2, 0, w_D5b4c0w21_2_0), (2, 1, w_D5b4c0w21_2_1), (2, 2, w_D5b4c0w21_2_2)]

theorem hwits_D5b4c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 4 0 (-2) (-1) wits_D5b4c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_0_0) (by rfl)]
      exact hcell_D5b4c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_0_1) (by rfl)]
      exact hcell_D5b4c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_0_2) (by rfl)]
      exact hcell_D5b4c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_1_0) (by rfl)]
      exact hcell_D5b4c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_1_1) (by rfl)]
      exact hcell_D5b4c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_1_2) (by rfl)]
      exact hcell_D5b4c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_2_0) (by rfl)]
      exact hcell_D5b4c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_2_1) (by rfl)]
      exact hcell_D5b4c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c0w21_2_2) (by rfl)]
      exact hcell_D5b4c0w21_2_2

@[expose] def w_D5b4c1_0_0 : GGResQTwoCell 5 :=
  .commonKernel [1, 2, 2, 1, 1, 1]

@[expose] def w_D5b4c1_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c1.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c1_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c1.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c1_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c1.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c1_1_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 2, 1, 2, 1]

@[expose] def w_D5b4c1_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c1.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c1_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c1.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c1_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c1.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c1_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [0, 0, 2, 1, 0, 1] Rq2_18423184c7c41865 [5, 1, 0, 2, 1, 4, 5, 4, 1, 2, 0, 1, 5] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b4c1_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 4 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [0, 0, 2, 1, 0, 1] [5, 1, 0, 2, 1, 4, 5, 4, 1, 2, 0, 1, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b4c1_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b4c1_0_0) = true := by
  rw [show w_D5b4c1_0_0 = .commonKernel [1, 2, 2, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 2, 1, 1, 1]) (by decide +kernel)

theorem hcell_D5b4c1_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b4c1_0_1) = true := by
  rw [show w_D5b4c1_0_1 = .reuse ((GGResIShape.D5b4c1.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c1.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c1.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c1_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b4c1_0_2) = true := by
  rw [show w_D5b4c1_0_2 = .reuse ((GGResIShape.D5b4c1.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c1.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c1.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c1_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b4c1_1_0) = true := by
  rw [show w_D5b4c1_1_0 = .reuse ((GGResIShape.D5b4c1.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c1.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c1.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c1_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b4c1_1_1) = true := by
  rw [show w_D5b4c1_1_1 = .commonKernel [2, 1, 2, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 2, 1, 2, 1]) (by decide +kernel)

theorem hcell_D5b4c1_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b4c1_1_2) = true := by
  rw [show w_D5b4c1_1_2 = .reuse ((GGResIShape.D5b4c1.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c1.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c1.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c1.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c1_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b4c1_2_0) = true := by
  rw [show w_D5b4c1_2_0 = .reuse ((GGResIShape.D5b4c1.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c1.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c1.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c1_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b4c1_2_1) = true := by
  rw [show w_D5b4c1_2_1 = .reuse ((GGResIShape.D5b4c1.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c1.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c1.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c1_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b4c1_2_2) = true := by
  rw [show w_D5b4c1_2_2 = .norm [0, 1, 2, 3, 4] [0, 0, 2, 1, 0, 1] Rq2_18423184c7c41865 [5, 1, 0, 2, 1, 4, 5, 4, 1, 2, 0, 1, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [0, 0, 2, 1, 0, 1] Rq2_18423184c7c41865 [5, 1, 0, 2, 1, 4, 5, 4, 1, 2, 0, 1, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b4c1_2_2

@[expose] def wits_D5b4c1 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b4c1_0_0), (0, 1, w_D5b4c1_0_1), (0, 2, w_D5b4c1_0_2), (1, 0, w_D5b4c1_1_0), (1, 1, w_D5b4c1_1_1), (1, 2, w_D5b4c1_1_2), (2, 0, w_D5b4c1_2_0), (2, 1, w_D5b4c1_2_1), (2, 2, w_D5b4c1_2_2)]

theorem hwits_D5b4c1 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 4 1 (-1) (-1) wits_D5b4c1 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_0_0) (by rfl)]
      exact hcell_D5b4c1_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_0_1) (by rfl)]
      exact hcell_D5b4c1_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_0_2) (by rfl)]
      exact hcell_D5b4c1_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_1_0) (by rfl)]
      exact hcell_D5b4c1_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_1_1) (by rfl)]
      exact hcell_D5b4c1_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_1_2) (by rfl)]
      exact hcell_D5b4c1_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_2_0) (by rfl)]
      exact hcell_D5b4c1_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_2_1) (by rfl)]
      exact hcell_D5b4c1_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c1_2_2) (by rfl)]
      exact hcell_D5b4c1_2_2

@[expose] def w_D5b4c3_0_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3_1_0 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 0, 2, 0, 1]

@[expose] def w_D5b4c3_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3_2_0 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 0, 2, 0, 1]

@[expose] def w_D5b4c3_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3_2_2 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 2, 0, 2, 2, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 5, 4, 3, 5, 2, 3, 1, 2, 4, 5] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b4c3_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 4 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [1, 2, 0, 2, 2, 1] [5, 3, 2, 1, 4, 2, 5, 4, 3, 5, 2, 3, 1, 2, 4, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b4c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b4c3_0_0) = true := by
  rw [show w_D5b4c3_0_0 = .reuse ((GGResIShape.D5b4c3.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c3.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b4c3_0_1) = true := by
  rw [show w_D5b4c3_0_1 = .reuse ((GGResIShape.D5b4c3.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c3.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b4c3_0_2) = true := by
  rw [show w_D5b4c3_0_2 = .reuse ((GGResIShape.D5b4c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b4c3_1_0) = true := by
  rw [show w_D5b4c3_1_0 = .commonKernel [2, 1, 0, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 0, 1]) (by decide +kernel)

theorem hcell_D5b4c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b4c3_1_1) = true := by
  rw [show w_D5b4c3_1_1 = .reuse ((GGResIShape.D5b4c3.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c3.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b4c3_1_2) = true := by
  rw [show w_D5b4c3_1_2 = .reuse ((GGResIShape.D5b4c3.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c3.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b4c3_2_0) = true := by
  rw [show w_D5b4c3_2_0 = .commonKernel [2, 1, 0, 2, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 0, 1]) (by decide +kernel)

theorem hcell_D5b4c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b4c3_2_1) = true := by
  rw [show w_D5b4c3_2_1 = .reuse ((GGResIShape.D5b4c3.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c3.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b4c3_2_2) = true := by
  rw [show w_D5b4c3_2_2 = .norm [0, 1, 2, 3, 4] [1, 2, 0, 2, 2, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 5, 4, 3, 5, 2, 3, 1, 2, 4, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 2, 0, 2, 2, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 5, 4, 3, 5, 2, 3, 1, 2, 4, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b4c3_2_2

@[expose] def wits_D5b4c3 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b4c3_0_0), (0, 1, w_D5b4c3_0_1), (0, 2, w_D5b4c3_0_2), (1, 0, w_D5b4c3_1_0), (1, 1, w_D5b4c3_1_1), (1, 2, w_D5b4c3_1_2), (2, 0, w_D5b4c3_2_0), (2, 1, w_D5b4c3_2_1), (2, 2, w_D5b4c3_2_2)]

theorem hwits_D5b4c3 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 4 3 (-1) (-1) wits_D5b4c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_0_0) (by rfl)]
      exact hcell_D5b4c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_0_1) (by rfl)]
      exact hcell_D5b4c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_0_2) (by rfl)]
      exact hcell_D5b4c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_1_0) (by rfl)]
      exact hcell_D5b4c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_1_1) (by rfl)]
      exact hcell_D5b4c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_1_2) (by rfl)]
      exact hcell_D5b4c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_2_0) (by rfl)]
      exact hcell_D5b4c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_2_1) (by rfl)]
      exact hcell_D5b4c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3_2_2) (by rfl)]
      exact hcell_D5b4c3_2_2

@[expose] def w_D5b4c3w12_0_0 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 0, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 5] 0

@[expose] def w_D5b4c3w12_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w12_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w12_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w12_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w12.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w12_1_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w12_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w12_2_1 : GGResQTwoCell 5 :=
  .commonKernel [2, 1, 0, 1, 1, 1]

@[expose] def w_D5b4c3w12_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w12.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b4c3w12_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 4 3 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [1, 2, 0, 1, 0, 1] [5, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b4c3w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_D5b4c3w12_0_0) = true := by
  rw [show w_D5b4c3w12_0_0 = .norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 0, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [1, 2, 0, 1, 0, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b4c3w12_0_0

theorem hcell_D5b4c3w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_D5b4c3w12_0_1) = true := by
  rw [show w_D5b4c3w12_0_1 = .reuse ((GGResIShape.D5b4c3w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c3w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_D5b4c3w12_0_2) = true := by
  rw [show w_D5b4c3w12_0_2 = .reuse ((GGResIShape.D5b4c3w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c3w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_D5b4c3w12_1_0) = true := by
  rw [show w_D5b4c3w12_1_0 = .reuse ((GGResIShape.D5b4c3w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c3w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_D5b4c3w12_1_1) = true := by
  rw [show w_D5b4c3w12_1_1 = .reuse ((GGResIShape.D5b4c3w12.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w12.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c3w12.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_D5b4c3w12_1_2) = true := by
  rw [show w_D5b4c3w12_1_2 = .reuse ((GGResIShape.D5b4c3w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c3w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_D5b4c3w12_2_0) = true := by
  rw [show w_D5b4c3w12_2_0 = .reuse ((GGResIShape.D5b4c3w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c3w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_D5b4c3w12_2_1) = true := by
  rw [show w_D5b4c3w12_2_1 = .commonKernel [2, 1, 0, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 1, 1, 1]) (by decide +kernel)

theorem hcell_D5b4c3w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_D5b4c3w12_2_2) = true := by
  rw [show w_D5b4c3w12_2_2 = .reuse ((GGResIShape.D5b4c3w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c3w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D5b4c3w12 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b4c3w12_0_0), (0, 1, w_D5b4c3w12_0_1), (0, 2, w_D5b4c3w12_0_2), (1, 0, w_D5b4c3w12_1_0), (1, 1, w_D5b4c3w12_1_1), (1, 2, w_D5b4c3w12_1_2), (2, 0, w_D5b4c3w12_2_0), (2, 1, w_D5b4c3w12_2_1), (2, 2, w_D5b4c3w12_2_2)]

theorem hwits_D5b4c3w12 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 4 3 (-1) (-2) wits_D5b4c3w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_0_0) (by rfl)]
      exact hcell_D5b4c3w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_0_1) (by rfl)]
      exact hcell_D5b4c3w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_0_2) (by rfl)]
      exact hcell_D5b4c3w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_1_0) (by rfl)]
      exact hcell_D5b4c3w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_1_1) (by rfl)]
      exact hcell_D5b4c3w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_1_2) (by rfl)]
      exact hcell_D5b4c3w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_2_0) (by rfl)]
      exact hcell_D5b4c3w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_2_1) (by rfl)]
      exact hcell_D5b4c3w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w12_2_2) (by rfl)]
      exact hcell_D5b4c3w12_2_2

@[expose] def w_D5b4c3w21_0_0 : GGResQTwoCell 5 :=
  .norm [0, 1, 2, 3, 4] [2, 1, 0, 2, 0, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 5] 0

@[expose] def w_D5b4c3w21_0_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w21_0_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w21_1_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w21_1_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w21_1_2 : GGResQTwoCell 5 :=
  .commonKernel [1, 2, 0, 2, 2, 1]

@[expose] def w_D5b4c3w21_2_0 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w21_2_1 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_D5b4c3w21_2_2 : GGResQTwoCell 5 :=
  .reuse ((GGResIShape.D5b4c3w21.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_D5b4c3w21_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.D 5) 4 3 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4] Rq2_18423184c7c41865 [2, 1, 0, 2, 0, 1] [5, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 5] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataD5) (by decide +kernel)
    (by decide +kernel) (pkListD5 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_D5b4c3w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_D5b4c3w21_0_0) = true := by
  rw [show w_D5b4c3w21_0_0 = .norm [0, 1, 2, 3, 4] [2, 1, 0, 2, 0, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 5] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4] [2, 1, 0, 2, 0, 1] Rq2_18423184c7c41865 [5, 3, 2, 1, 4, 2, 3, 5, 3, 2, 4, 1, 2, 3, 5] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_D5b4c3w21_0_0

theorem hcell_D5b4c3w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_D5b4c3w21_0_1) = true := by
  rw [show w_D5b4c3w21_0_1 = .reuse ((GGResIShape.D5b4c3w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c3w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_D5b4c3w21_0_2) = true := by
  rw [show w_D5b4c3w21_0_2 = .reuse ((GGResIShape.D5b4c3w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c3w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_D5b4c3w21_1_0) = true := by
  rw [show w_D5b4c3w21_1_0 = .reuse ((GGResIShape.D5b4c3w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c3w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_D5b4c3w21_1_1) = true := by
  rw [show w_D5b4c3w21_1_1 = .reuse ((GGResIShape.D5b4c3w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c3w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_D5b4c3w21_1_2) = true := by
  rw [show w_D5b4c3w21_1_2 = .commonKernel [1, 2, 0, 2, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 2, 2, 1]) (by decide +kernel)

theorem hcell_D5b4c3w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_D5b4c3w21_2_0) = true := by
  rw [show w_D5b4c3w21_2_0 = .reuse ((GGResIShape.D5b4c3w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.D5b4c3w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_D5b4c3w21_2_1) = true := by
  rw [show w_D5b4c3w21_2_1 = .reuse ((GGResIShape.D5b4c3w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.D5b4c3w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_D5b4c3w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.D 5) 4 3 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_D5b4c3w21_2_2) = true := by
  rw [show w_D5b4c3w21_2_2 = .reuse ((GGResIShape.D5b4c3w21.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.D5b4c3w21.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.D5b4c3w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.D5b4c3w21.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_D5b4c3w21 : List (ℕ × ℕ × GGResQTwoCell 5) :=
  [(0, 0, w_D5b4c3w21_0_0), (0, 1, w_D5b4c3w21_0_1), (0, 2, w_D5b4c3w21_0_2), (1, 0, w_D5b4c3w21_1_0), (1, 1, w_D5b4c3w21_1_1), (1, 2, w_D5b4c3w21_1_2), (2, 0, w_D5b4c3w21_2_0), (2, 1, w_D5b4c3w21_2_1), (2, 2, w_D5b4c3w21_2_2)]

theorem hwits_D5b4c3w21 :
    GGResQTwoCellCheckAll (CartanMatrix.D 5) 4 3 (-2) (-1) wits_D5b4c3w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_0_0) (by rfl)]
      exact hcell_D5b4c3w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_0_1) (by rfl)]
      exact hcell_D5b4c3w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_0_2) (by rfl)]
      exact hcell_D5b4c3w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_1_0) (by rfl)]
      exact hcell_D5b4c3w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_1_1) (by rfl)]
      exact hcell_D5b4c3w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_1_2) (by rfl)]
      exact hcell_D5b4c3w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_2_0) (by rfl)]
      exact hcell_D5b4c3w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_2_1) (by rfl)]
      exact hcell_D5b4c3w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_D5b4c3w21_2_2) (by rfl)]
      exact hcell_D5b4c3w21_2_2

@[expose] def wits_D5_b0 (s : Fin 5 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 5) :=
  if s = (3, -1, -1) then wits_D5b0c3
  else if s = (4, -1, -1) then wits_D5b0c4
  else []

theorem cell_D5_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.D 5) 0 (GGResIDisp.D5.shapes_D5_b0) (wits_D5_b0) := by
  intro s hs
  simp only [GGResIDisp.D5.shapes_D5_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · simp only [wits_D5_b0, if_pos rfl]
    exact hwits_D5b0c3
  · simp only [wits_D5_b0, if_neg (by decide : ¬ (((4, -1, -1)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_D5b0c4
theorem hsideOK_D5_b0 :
    ∀ s ∈ GGResIDisp.D5.shapes_D5_b0, ∀ w ∈ wits_D5_b0 s,
      ggResQTwoCellSideOK (0 : Fin 5) w.2.2 := by
  have hall : (GGResIDisp.D5.shapes_D5_b0.all fun s => (wits_D5_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 5) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D5_b0 :
    ∀ s ∈ GGResIDisp.D5.shapes_D5_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D5.shapes_D5_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def wits_D5_b3 (s : Fin 5 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 5) :=
  if s = (0, -1, -1) then wits_D5b3c0
  else if s = (0, -1, -2) then wits_D5b3c0w12
  else if s = (0, -2, -1) then wits_D5b3c0w21
  else if s = (1, -1, -1) then wits_D5b3c1
  else if s = (4, -1, -1) then wits_D5b3c4
  else if s = (4, -1, -2) then wits_D5b3c4w12
  else if s = (4, -2, -1) then wits_D5b3c4w21
  else []

theorem cell_D5_b3 :
    GGResQTwoShapeCoverage (CartanMatrix.D 5) 3 (GGResIDisp.D5.shapes_D5_b3) (wits_D5_b3) := by
  intro s hs
  simp only [GGResIDisp.D5.shapes_D5_b3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_D5_b3, if_pos rfl]
    exact hwits_D5b3c0
  · simp only [wits_D5_b3, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_D5b3c0w12
  · simp only [wits_D5_b3, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_D5b3c0w21
  · simp only [wits_D5_b3, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_D5b3c1
  · simp only [wits_D5_b3, if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_D5b3c4
  · simp only [wits_D5_b3, if_neg (by decide : ¬ (((4, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((4, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((4, -1, -2)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -2)) = ((4, -1, -1)))), if_pos rfl]
    exact hwits_D5b3c4w12
  · simp only [wits_D5_b3, if_neg (by decide : ¬ (((4, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((4, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((4, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((4, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((4, -2, -1)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((4, -2, -1)) = ((4, -1, -2)))), if_pos rfl]
    exact hwits_D5b3c4w21
theorem hsideOK_D5_b3 :
    ∀ s ∈ GGResIDisp.D5.shapes_D5_b3, ∀ w ∈ wits_D5_b3 s,
      ggResQTwoCellSideOK (3 : Fin 5) w.2.2 := by
  have hall : (GGResIDisp.D5.shapes_D5_b3.all fun s => (wits_D5_b3 s).all fun w =>
      ggResQTwoCellSideOKB (3 : Fin 5) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D5_b3 :
    ∀ s ∈ GGResIDisp.D5.shapes_D5_b3, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D5.shapes_D5_b3.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def wits_D5_b4 (s : Fin 5 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 5) :=
  if s = (0, -1, -1) then wits_D5b4c0
  else if s = (0, -1, -2) then wits_D5b4c0w12
  else if s = (0, -2, -1) then wits_D5b4c0w21
  else if s = (1, -1, -1) then wits_D5b4c1
  else if s = (3, -1, -1) then wits_D5b4c3
  else if s = (3, -1, -2) then wits_D5b4c3w12
  else if s = (3, -2, -1) then wits_D5b4c3w21
  else []

theorem cell_D5_b4 :
    GGResQTwoShapeCoverage (CartanMatrix.D 5) 4 (GGResIDisp.D5.shapes_D5_b4) (wits_D5_b4) := by
  intro s hs
  simp only [GGResIDisp.D5.shapes_D5_b4, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_D5_b4, if_pos rfl]
    exact hwits_D5b4c0
  · simp only [wits_D5_b4, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_D5b4c0w12
  · simp only [wits_D5_b4, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_D5b4c0w21
  · simp only [wits_D5_b4, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_D5b4c1
  · simp only [wits_D5_b4, if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_D5b4c3
  · simp only [wits_D5_b4, if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -2)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_D5b4c3w12
  · simp only [wits_D5_b4, if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((3, -2, -1)) = ((3, -1, -2)))), if_pos rfl]
    exact hwits_D5b4c3w21
theorem hsideOK_D5_b4 :
    ∀ s ∈ GGResIDisp.D5.shapes_D5_b4, ∀ w ∈ wits_D5_b4 s,
      ggResQTwoCellSideOK (4 : Fin 5) w.2.2 := by
  have hall : (GGResIDisp.D5.shapes_D5_b4.all fun s => (wits_D5_b4 s).all fun w =>
      ggResQTwoCellSideOKB (4 : Fin 5) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D5_b4 :
    ∀ s ∈ GGResIDisp.D5.shapes_D5_b4, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D5.shapes_D5_b4.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataD5
