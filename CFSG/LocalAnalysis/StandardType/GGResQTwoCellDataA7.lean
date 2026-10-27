module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataA7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_0777788aee31d1c4 : List (Fin 8 × List (Fin 8)) :=
[(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (6, []), (0, [1]), (1, [2]), (2, [3]), (3, [4]), (4, [5]), (5, [6]), (0, [2, 1]), (1, [3, 2]), (2, [4, 3]), (3, [5, 4]), (4, [6, 5]), (0, [3, 2, 1]), (1, [4, 3, 2]), (2, [5, 4, 3]), (3, [6, 5, 4]), (0, [4, 3, 2, 1]), (1, [5, 4, 3, 2]), (2, [6, 5, 4, 3]), (0, [5, 4, 3, 2, 1]), (1, [6, 5, 4, 3, 2]), (0, [6, 5, 4, 3, 2, 1])]

@[expose] def pkTabA7 : ℕ := 198083100200460565896497889290

@[expose] def pkDataA7 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 79229371458530977775699968002),
  (4, 4, 79229371458530977776773758981),
  (16, 16, 79229371458531048148739358721),
  (64, 64, 79229371463142945286283919361),
  (256, 256, 79229673708433751406610022401),
  (1024, 1024, 99037621086703653098098851841),
  (4096, 4096, 158462369676073773885942726657),
  (5, 5, 79229371458530977777042096136),
  (20, 20, 79229371458531065734483148821),
  (80, 80, 79229371464295444591311912961),
  (320, 320, 79229749238628205721198592001),
  (1280, 1280, 103987567910461613974596157441),
  (5120, 5120, 39623753051070992857341952001),
  (21, 21, 79229371458531070133066072104),
  (84, 84, 79229371464583710121772187733),
  (336, 336, 79229768130398009965766049793),
  (1344, 1344, 105225658936352585947510013953),
  (5376, 5376, 49518811235128513950837178369),
  (85, 85, 79229371464655776511900582056),
  (340, 340, 79229772853340953420216402261),
  (1360, 1360, 105535181725094816805809356801),
  (5440, 5440, 51994690594299619509318778881),
  (341, 341, 79229774034076689325692617384),
  (1364, 1364, 105612562422283118095043659093),
  (5456, 5456, 52613660613895304781740965889),
  (1365, 1365, 105631907596580193596617067176),
  (5460, 5460, 52768403118805974399909893461),
  (5461, 5461, 52807088745033642533321779880)]

theorem pkTabA7_spec : ∀ a b : Fin 7, ((CartanMatrix.A 7 a b : ℤ) : ZMod 3) =
    ((GGResQTwoPacked.pkLane pkTabA7 (a.val * 7 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedA7 : GGResQTwoPacked.pkSharedOK pkTabA7 7 ([0, 1, 2, 3, 4, 5, 6] : List (Fin 8))
    Rq2_0777788aee31d1c4 pkDataA7 = true := by
  decide +kernel

theorem pkListA7 (ib ic : Fin 7) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.A 7) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.A 7) ib ic e₁ e₂ u v k).get
      (Fin.last 8) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.A 7) ib ic e₁ e₂ u v)
        [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 ∧
      ∀ r ∈ Rq2_0777788aee31d1c4, ∃ d ∈ pkDataA7, GGResQTwoPacked.pkBlkM 7
        (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.A 7) ib ic e₁ e₂ u v) r) = d.2.2 :=
  GGResQTwoPacked.pkShared_sound pkSharedA7 (GGResQTwoPacked.pkTab_std pkTabA7_spec ib ic e₁ e₂ u v)
    h2 hx

@[expose] def w_A7b0c1w12_0_0 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 1, 2, 0, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3

@[expose] def w_A7b0c1w12_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w12_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w12_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w12_1_1 : GGResQTwoCell 7 :=
  .commonKernel [1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def w_A7b0c1w12_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w12_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w12_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 0, 0, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3

@[expose] def w_A7b0c1w12_2_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w12.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c1w12_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 1 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 0, 1, 2, 0, 1, 2, 1] [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c1w12_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 1 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 0, 0, 0, 0, 0, 0, 1] [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b0c1w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c1w12_0_0) = true := by
  rw [show w_A7b0c1w12_0_0 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 1, 2, 0, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 1, 2, 0, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c1w12_0_0

theorem hcell_A7b0c1w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c1w12_0_1) = true := by
  rw [show w_A7b0c1w12_0_1 = .reuse ((GGResIShape.A7b0c1w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c1w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c1w12_0_2) = true := by
  rw [show w_A7b0c1w12_0_2 = .reuse ((GGResIShape.A7b0c1w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c1w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c1w12_1_0) = true := by
  rw [show w_A7b0c1w12_1_0 = .reuse ((GGResIShape.A7b0c1w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c1w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c1w12_1_1) = true := by
  rw [show w_A7b0c1w12_1_1 = .commonKernel [1, 0, 0, 0, 0, 0, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

theorem hcell_A7b0c1w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c1w12_1_2) = true := by
  rw [show w_A7b0c1w12_1_2 = .reuse ((GGResIShape.A7b0c1w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c1w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c1w12_2_0) = true := by
  rw [show w_A7b0c1w12_2_0 = .reuse ((GGResIShape.A7b0c1w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c1w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c1w12_2_1) = true := by
  rw [show w_A7b0c1w12_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 0, 0, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 0, 0, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c1w12_2_1

theorem hcell_A7b0c1w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c1w12_2_2) = true := by
  rw [show w_A7b0c1w12_2_2 = .reuse ((GGResIShape.A7b0c1w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c1w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_A7b0c1w12 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c1w12_0_0), (0, 1, w_A7b0c1w12_0_1), (0, 2, w_A7b0c1w12_0_2), (1, 0, w_A7b0c1w12_1_0), (1, 1, w_A7b0c1w12_1_1), (1, 2, w_A7b0c1w12_1_2), (2, 0, w_A7b0c1w12_2_0), (2, 1, w_A7b0c1w12_2_1), (2, 2, w_A7b0c1w12_2_2)]

theorem hwits_A7b0c1w12 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 1 (-1) (-2) wits_A7b0c1w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_0_0) (by rfl)]
      exact hcell_A7b0c1w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_0_1) (by rfl)]
      exact hcell_A7b0c1w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_0_2) (by rfl)]
      exact hcell_A7b0c1w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_1_0) (by rfl)]
      exact hcell_A7b0c1w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_1_1) (by rfl)]
      exact hcell_A7b0c1w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_1_2) (by rfl)]
      exact hcell_A7b0c1w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_2_0) (by rfl)]
      exact hcell_A7b0c1w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_2_1) (by rfl)]
      exact hcell_A7b0c1w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w12_2_2) (by rfl)]
      exact hcell_A7b0c1w12_2_2

@[expose] def w_A7b0c1w21_0_0 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 2, 1, 0, 2, 1, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3

@[expose] def w_A7b0c1w21_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w21_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w21_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w21_1_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w21_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 0, 0, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3

@[expose] def w_A7b0c1w21_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w21_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c1w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c1w21_2_2 : GGResQTwoCell 7 :=
  .commonKernel [2, 0, 0, 0, 0, 0, 0, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c1w21_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 1 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 0, 2, 1, 0, 2, 1, 1] [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c1w21_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 1 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 0, 0, 0, 0, 0, 0, 1] [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b0c1w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c1w21_0_0) = true := by
  rw [show w_A7b0c1w21_0_0 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 2, 1, 0, 2, 1, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 2, 1, 0, 2, 1, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c1w21_0_0

theorem hcell_A7b0c1w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c1w21_0_1) = true := by
  rw [show w_A7b0c1w21_0_1 = .reuse ((GGResIShape.A7b0c1w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c1w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c1w21_0_2) = true := by
  rw [show w_A7b0c1w21_0_2 = .reuse ((GGResIShape.A7b0c1w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c1w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c1w21_1_0) = true := by
  rw [show w_A7b0c1w21_1_0 = .reuse ((GGResIShape.A7b0c1w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c1w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c1w21_1_1) = true := by
  rw [show w_A7b0c1w21_1_1 = .reuse ((GGResIShape.A7b0c1w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c1w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c1w21_1_2) = true := by
  rw [show w_A7b0c1w21_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 0, 0, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 0, 0, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 7, 1, 2, 0, 1, 7] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c1w21_1_2

theorem hcell_A7b0c1w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c1w21_2_0) = true := by
  rw [show w_A7b0c1w21_2_0 = .reuse ((GGResIShape.A7b0c1w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c1w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c1w21_2_1) = true := by
  rw [show w_A7b0c1w21_2_1 = .reuse ((GGResIShape.A7b0c1w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c1w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c1w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c1w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c1w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 1 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c1w21_2_2) = true := by
  rw [show w_A7b0c1w21_2_2 = .commonKernel [2, 0, 0, 0, 0, 0, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def wits_A7b0c1w21 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c1w21_0_0), (0, 1, w_A7b0c1w21_0_1), (0, 2, w_A7b0c1w21_0_2), (1, 0, w_A7b0c1w21_1_0), (1, 1, w_A7b0c1w21_1_1), (1, 2, w_A7b0c1w21_1_2), (2, 0, w_A7b0c1w21_2_0), (2, 1, w_A7b0c1w21_2_1), (2, 2, w_A7b0c1w21_2_2)]

theorem hwits_A7b0c1w21 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 1 (-2) (-1) wits_A7b0c1w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_0_0) (by rfl)]
      exact hcell_A7b0c1w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_0_1) (by rfl)]
      exact hcell_A7b0c1w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_0_2) (by rfl)]
      exact hcell_A7b0c1w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_1_0) (by rfl)]
      exact hcell_A7b0c1w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_1_1) (by rfl)]
      exact hcell_A7b0c1w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_1_2) (by rfl)]
      exact hcell_A7b0c1w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_2_0) (by rfl)]
      exact hcell_A7b0c1w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_2_1) (by rfl)]
      exact hcell_A7b0c1w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c1w21_2_2) (by rfl)]
      exact hcell_A7b0c1w21_2_2

@[expose] def w_A7b0c2_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c2.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c2_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c2.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c2_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c2.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c2_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c2.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c2_1_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c2.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c2_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c2.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c2_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c2.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c2_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c2.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c2_2_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 2, 0, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 2, 1, 3, 2, 7, 2, 3, 1, 2, 0, 7] 1

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c2_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 2, 1, 2, 0, 1, 2, 1] [7, 0, 2, 1, 3, 2, 7, 2, 3, 1, 2, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b0c2_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c2_0_0) = true := by
  rw [show w_A7b0c2_0_0 = .reuse ((GGResIShape.A7b0c2.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c2.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c2.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c2_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c2_0_1) = true := by
  rw [show w_A7b0c2_0_1 = .reuse ((GGResIShape.A7b0c2.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c2.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c2.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c2_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c2_0_2) = true := by
  rw [show w_A7b0c2_0_2 = .reuse ((GGResIShape.A7b0c2.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c2.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c2.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c2_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c2_1_0) = true := by
  rw [show w_A7b0c2_1_0 = .reuse ((GGResIShape.A7b0c2.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c2.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c2.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c2_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c2_1_1) = true := by
  rw [show w_A7b0c2_1_1 = .reuse ((GGResIShape.A7b0c2.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c2.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c2.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c2_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c2_1_2) = true := by
  rw [show w_A7b0c2_1_2 = .reuse ((GGResIShape.A7b0c2.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c2.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c2.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c2_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c2_2_0) = true := by
  rw [show w_A7b0c2_2_0 = .reuse ((GGResIShape.A7b0c2.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c2.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c2.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c2_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c2_2_1) = true := by
  rw [show w_A7b0c2_2_1 = .reuse ((GGResIShape.A7b0c2.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c2.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c2.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c2_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c2_2_2) = true := by
  rw [show w_A7b0c2_2_2 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 2, 0, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 2, 1, 3, 2, 7, 2, 3, 1, 2, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 2, 0, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 2, 1, 3, 2, 7, 2, 3, 1, 2, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c2_2_2

@[expose] def wits_A7b0c2 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c2_0_0), (0, 1, w_A7b0c2_0_1), (0, 2, w_A7b0c2_0_2), (1, 0, w_A7b0c2_1_0), (1, 1, w_A7b0c2_1_1), (1, 2, w_A7b0c2_1_2), (2, 0, w_A7b0c2_2_0), (2, 1, w_A7b0c2_2_1), (2, 2, w_A7b0c2_2_2)]

theorem hwits_A7b0c2 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 2 (-1) (-1) wits_A7b0c2 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_0_0) (by rfl)]
      exact hcell_A7b0c2_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_0_1) (by rfl)]
      exact hcell_A7b0c2_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_0_2) (by rfl)]
      exact hcell_A7b0c2_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_1_0) (by rfl)]
      exact hcell_A7b0c2_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_1_1) (by rfl)]
      exact hcell_A7b0c2_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_1_2) (by rfl)]
      exact hcell_A7b0c2_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_2_0) (by rfl)]
      exact hcell_A7b0c2_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_2_1) (by rfl)]
      exact hcell_A7b0c2_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c2_2_2) (by rfl)]
      exact hcell_A7b0c2_2_2

@[expose] def w_A7b0c3_0_0 : GGResQTwoCell 7 :=
  .commonKernel [2, 1, 0, 2, 0, 1, 2, 1]

@[expose] def w_A7b0c3_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c3_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c3_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c3_1_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 3, 2, 4, 3, 5, 4, 6, 5, 7, 0, 3, 2, 4, 3, 7, 3, 4, 2, 3, 0, 7, 5, 6, 4, 5, 3, 4, 2, 3, 7] 0

@[expose] def w_A7b0c3_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c3.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c3_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c3_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c3.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c3_2_2 : GGResQTwoCell 7 :=
  .commonKernel [1, 1, 1, 1, 0, 2, 1, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c3_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 1, 2, 0, 0, 0, 0, 1] [7, 3, 2, 4, 3, 5, 4, 6, 5, 7, 0, 3, 2, 4, 3, 7, 3, 4, 2, 3, 0, 7, 5, 6, 4, 5, 3, 4, 2, 3, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b0c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c3_0_0) = true := by
  rw [show w_A7b0c3_0_0 = .commonKernel [2, 1, 0, 2, 0, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 0, 1, 2, 1]) (by decide +kernel)

theorem hcell_A7b0c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c3_0_1) = true := by
  rw [show w_A7b0c3_0_1 = .reuse ((GGResIShape.A7b0c3.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c3.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c3.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c3_0_2) = true := by
  rw [show w_A7b0c3_0_2 = .reuse ((GGResIShape.A7b0c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c3_1_0) = true := by
  rw [show w_A7b0c3_1_0 = .reuse ((GGResIShape.A7b0c3.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c3.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c3.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c3_1_1) = true := by
  rw [show w_A7b0c3_1_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 3, 2, 4, 3, 5, 4, 6, 5, 7, 0, 3, 2, 4, 3, 7, 3, 4, 2, 3, 0, 7, 5, 6, 4, 5, 3, 4, 2, 3, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 0, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 3, 2, 4, 3, 5, 4, 6, 5, 7, 0, 3, 2, 4, 3, 7, 3, 4, 2, 3, 0, 7, 5, 6, 4, 5, 3, 4, 2, 3, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c3_1_1

theorem hcell_A7b0c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c3_1_2) = true := by
  rw [show w_A7b0c3_1_2 = .reuse ((GGResIShape.A7b0c3.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c3.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c3.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c3_2_0) = true := by
  rw [show w_A7b0c3_2_0 = .reuse ((GGResIShape.A7b0c3.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c3.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c3.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c3_2_1) = true := by
  rw [show w_A7b0c3_2_1 = .reuse ((GGResIShape.A7b0c3.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c3.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c3.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c3_2_2) = true := by
  rw [show w_A7b0c3_2_2 = .commonKernel [1, 1, 1, 1, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 0, 2, 1, 1]) (by decide +kernel)

@[expose] def wits_A7b0c3 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c3_0_0), (0, 1, w_A7b0c3_0_1), (0, 2, w_A7b0c3_0_2), (1, 0, w_A7b0c3_1_0), (1, 1, w_A7b0c3_1_1), (1, 2, w_A7b0c3_1_2), (2, 0, w_A7b0c3_2_0), (2, 1, w_A7b0c3_2_1), (2, 2, w_A7b0c3_2_2)]

theorem hwits_A7b0c3 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 3 (-1) (-1) wits_A7b0c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_0_0) (by rfl)]
      exact hcell_A7b0c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_0_1) (by rfl)]
      exact hcell_A7b0c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_0_2) (by rfl)]
      exact hcell_A7b0c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_1_0) (by rfl)]
      exact hcell_A7b0c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_1_1) (by rfl)]
      exact hcell_A7b0c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_1_2) (by rfl)]
      exact hcell_A7b0c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_2_0) (by rfl)]
      exact hcell_A7b0c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_2_1) (by rfl)]
      exact hcell_A7b0c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c3_2_2) (by rfl)]
      exact hcell_A7b0c3_2_2

@[expose] def w_A7b0c4_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c4.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c4_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c4.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c4_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c4.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c4_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c4.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c4_1_1 : GGResQTwoCell 7 :=
  .commonKernel [1, 0, 2, 1, 0, 1, 2, 1]

@[expose] def w_A7b0c4_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c4.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c4_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c4.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c4_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c4.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c4_2_2 : GGResQTwoCell 7 :=
  .commonKernel [2, 0, 1, 2, 0, 0, 0, 1]

theorem hcell_A7b0c4_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c4_0_0) = true := by
  rw [show w_A7b0c4_0_0 = .reuse ((GGResIShape.A7b0c4.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c4.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c4.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c4_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c4_0_1) = true := by
  rw [show w_A7b0c4_0_1 = .reuse ((GGResIShape.A7b0c4.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c4.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c4.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c4_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c4_0_2) = true := by
  rw [show w_A7b0c4_0_2 = .reuse ((GGResIShape.A7b0c4.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c4.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c4.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c4_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c4_1_0) = true := by
  rw [show w_A7b0c4_1_0 = .reuse ((GGResIShape.A7b0c4.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c4.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c4.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c4_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c4_1_1) = true := by
  rw [show w_A7b0c4_1_1 = .commonKernel [1, 0, 2, 1, 0, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 0, 2, 1, 0, 1, 2, 1]) (by decide +kernel)

theorem hcell_A7b0c4_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c4_1_2) = true := by
  rw [show w_A7b0c4_1_2 = .reuse ((GGResIShape.A7b0c4.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c4.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c4.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c4_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c4_2_0) = true := by
  rw [show w_A7b0c4_2_0 = .reuse ((GGResIShape.A7b0c4.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c4.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c4.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c4_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c4_2_1) = true := by
  rw [show w_A7b0c4_2_1 = .reuse ((GGResIShape.A7b0c4.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c4.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c4.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c4_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 4 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c4_2_2) = true := by
  rw [show w_A7b0c4_2_2 = .commonKernel [2, 0, 1, 2, 0, 0, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def wits_A7b0c4 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c4_0_0), (0, 1, w_A7b0c4_0_1), (0, 2, w_A7b0c4_0_2), (1, 0, w_A7b0c4_1_0), (1, 1, w_A7b0c4_1_1), (1, 2, w_A7b0c4_1_2), (2, 0, w_A7b0c4_2_0), (2, 1, w_A7b0c4_2_1), (2, 2, w_A7b0c4_2_2)]

theorem hwits_A7b0c4 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 4 (-1) (-1) wits_A7b0c4 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_0_0) (by rfl)]
      exact hcell_A7b0c4_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_0_1) (by rfl)]
      exact hcell_A7b0c4_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_0_2) (by rfl)]
      exact hcell_A7b0c4_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_1_0) (by rfl)]
      exact hcell_A7b0c4_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_1_1) (by rfl)]
      exact hcell_A7b0c4_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_1_2) (by rfl)]
      exact hcell_A7b0c4_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_2_0) (by rfl)]
      exact hcell_A7b0c4_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_2_1) (by rfl)]
      exact hcell_A7b0c4_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c4_2_2) (by rfl)]
      exact hcell_A7b0c4_2_2

@[expose] def w_A7b0c5_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c5.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c5_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c5.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c5_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c5.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c5_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c5.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c5_1_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 5, 4, 3, 7, 0, 5, 4, 6, 5, 7, 5, 6, 4, 5, 0, 7, 3, 4, 5, 1, 0, 7] 6

@[expose] def w_A7b0c5_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c5.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c5_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c5.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c5_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c5.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c5_2_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 2, 3, 5, 4, 6, 5, 7, 5, 6, 4, 5, 3, 2, 1, 0, 7] 1

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c5_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 5 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 2, 2, 2, 2, 2, 1, 1] [7, 0, 1, 5, 4, 3, 7, 0, 5, 4, 6, 5, 7, 5, 6, 4, 5, 0, 7, 3, 4, 5, 1, 0, 7] 6 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c5_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 5 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 2, 1, 0, 2, 1, 2, 1] [7, 0, 1, 2, 3, 5, 4, 6, 5, 7, 5, 6, 4, 5, 3, 2, 1, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b0c5_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c5_0_0) = true := by
  rw [show w_A7b0c5_0_0 = .reuse ((GGResIShape.A7b0c5.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c5.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c5.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c5.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c5_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c5_0_1) = true := by
  rw [show w_A7b0c5_0_1 = .reuse ((GGResIShape.A7b0c5.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c5.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c5.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c5.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c5_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c5_0_2) = true := by
  rw [show w_A7b0c5_0_2 = .reuse ((GGResIShape.A7b0c5.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c5.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c5.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c5.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c5_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c5_1_0) = true := by
  rw [show w_A7b0c5_1_0 = .reuse ((GGResIShape.A7b0c5.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c5.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c5.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c5.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c5_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c5_1_1) = true := by
  rw [show w_A7b0c5_1_1 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 5, 4, 3, 7, 0, 5, 4, 6, 5, 7, 5, 6, 4, 5, 0, 7, 3, 4, 5, 1, 0, 7] 6 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 5, 4, 3, 7, 0, 5, 4, 6, 5, 7, 5, 6, 4, 5, 0, 7, 3, 4, 5, 1, 0, 7] 6) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c5_1_1

theorem hcell_A7b0c5_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c5_1_2) = true := by
  rw [show w_A7b0c5_1_2 = .reuse ((GGResIShape.A7b0c5.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c5.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c5.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c5.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c5_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c5_2_0) = true := by
  rw [show w_A7b0c5_2_0 = .reuse ((GGResIShape.A7b0c5.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c5.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c5.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c5.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c5_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c5_2_1) = true := by
  rw [show w_A7b0c5_2_1 = .reuse ((GGResIShape.A7b0c5.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c5.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c5.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c5.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c5_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 5 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c5_2_2) = true := by
  rw [show w_A7b0c5_2_2 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 2, 3, 5, 4, 6, 5, 7, 5, 6, 4, 5, 3, 2, 1, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 2, 3, 5, 4, 6, 5, 7, 5, 6, 4, 5, 3, 2, 1, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c5_2_2

@[expose] def wits_A7b0c5 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c5_0_0), (0, 1, w_A7b0c5_0_1), (0, 2, w_A7b0c5_0_2), (1, 0, w_A7b0c5_1_0), (1, 1, w_A7b0c5_1_1), (1, 2, w_A7b0c5_1_2), (2, 0, w_A7b0c5_2_0), (2, 1, w_A7b0c5_2_1), (2, 2, w_A7b0c5_2_2)]

theorem hwits_A7b0c5 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 5 (-1) (-1) wits_A7b0c5 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_0_0) (by rfl)]
      exact hcell_A7b0c5_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_0_1) (by rfl)]
      exact hcell_A7b0c5_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_0_2) (by rfl)]
      exact hcell_A7b0c5_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_1_0) (by rfl)]
      exact hcell_A7b0c5_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_1_1) (by rfl)]
      exact hcell_A7b0c5_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_1_2) (by rfl)]
      exact hcell_A7b0c5_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_2_0) (by rfl)]
      exact hcell_A7b0c5_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_2_1) (by rfl)]
      exact hcell_A7b0c5_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c5_2_2) (by rfl)]
      exact hcell_A7b0c5_2_2

@[expose] def w_A7b0c6_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6_1_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2

@[expose] def w_A7b0c6_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2

@[expose] def w_A7b0c6_2_2 : GGResQTwoCell 7 :=
  .commonKernel [1, 1, 1, 1, 1, 1, 1, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 1, 1, 1, 1, 1, 1, 1] [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 1, 2, 0, 1, 2, 0, 1] [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b0c6_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c6_0_0) = true := by
  rw [show w_A7b0c6_0_0 = .reuse ((GGResIShape.A7b0c6.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c6_0_1) = true := by
  rw [show w_A7b0c6_0_1 = .reuse ((GGResIShape.A7b0c6.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c6.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c6.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c6_0_2) = true := by
  rw [show w_A7b0c6_0_2 = .reuse ((GGResIShape.A7b0c6.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c6.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c6.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c6_1_0) = true := by
  rw [show w_A7b0c6_1_0 = .reuse ((GGResIShape.A7b0c6.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c6_1_1) = true := by
  rw [show w_A7b0c6_1_1 = .reuse ((GGResIShape.A7b0c6.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c6.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c6.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c6_1_2) = true := by
  rw [show w_A7b0c6_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6_1_2

theorem hcell_A7b0c6_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c6_2_0) = true := by
  rw [show w_A7b0c6_2_0 = .reuse ((GGResIShape.A7b0c6.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c6_2_1) = true := by
  rw [show w_A7b0c6_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6_2_1

theorem hcell_A7b0c6_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c6_2_2) = true := by
  rw [show w_A7b0c6_2_2 = .commonKernel [1, 1, 1, 1, 1, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 1, 1, 1, 1]) (by decide +kernel)

@[expose] def wits_A7b0c6 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c6_0_0), (0, 1, w_A7b0c6_0_1), (0, 2, w_A7b0c6_0_2), (1, 0, w_A7b0c6_1_0), (1, 1, w_A7b0c6_1_1), (1, 2, w_A7b0c6_1_2), (2, 0, w_A7b0c6_2_0), (2, 1, w_A7b0c6_2_1), (2, 2, w_A7b0c6_2_2)]

theorem hwits_A7b0c6 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 6 (-1) (-1) wits_A7b0c6 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_0_0) (by rfl)]
      exact hcell_A7b0c6_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_0_1) (by rfl)]
      exact hcell_A7b0c6_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_0_2) (by rfl)]
      exact hcell_A7b0c6_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_1_0) (by rfl)]
      exact hcell_A7b0c6_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_1_1) (by rfl)]
      exact hcell_A7b0c6_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_1_2) (by rfl)]
      exact hcell_A7b0c6_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_2_0) (by rfl)]
      exact hcell_A7b0c6_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_2_1) (by rfl)]
      exact hcell_A7b0c6_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_2_2) (by rfl)]
      exact hcell_A7b0c6_2_2

@[expose] def w_A7b0c6w12_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w12.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w12_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w12_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w12_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w12_1_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0

@[expose] def w_A7b0c6w12_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1

@[expose] def w_A7b0c6w12_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w12_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1

@[expose] def w_A7b0c6w12_2_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6w12_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 2, 2, 2, 2, 2, 2, 1] [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6w12_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 2, 1, 0, 2, 1, 0, 1] [7, 0, 6, 7, 6, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6w12_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 2, 2, 2, 2, 2, 2, 1] [7, 0, 6, 7, 6, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6w12_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 2, 1, 0, 2, 1, 0, 1] [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b0c6w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c6w12_0_0) = true := by
  rw [show w_A7b0c6w12_0_0 = .reuse ((GGResIShape.A7b0c6w12.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w12.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6w12.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c6w12_0_1) = true := by
  rw [show w_A7b0c6w12_0_1 = .reuse ((GGResIShape.A7b0c6w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c6w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c6w12_0_2) = true := by
  rw [show w_A7b0c6w12_0_2 = .reuse ((GGResIShape.A7b0c6w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c6w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c6w12_1_0) = true := by
  rw [show w_A7b0c6w12_1_0 = .reuse ((GGResIShape.A7b0c6w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c6w12_1_1) = true := by
  rw [show w_A7b0c6w12_1_1 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6w12_1_1

theorem hcell_A7b0c6w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c6w12_1_2) = true := by
  rw [show w_A7b0c6w12_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6w12_1_2

theorem hcell_A7b0c6w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c6w12_2_0) = true := by
  rw [show w_A7b0c6w12_2_0 = .reuse ((GGResIShape.A7b0c6w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c6w12_2_1) = true := by
  rw [show w_A7b0c6w12_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6w12_2_1

theorem hcell_A7b0c6w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c6w12_2_2) = true := by
  rw [show w_A7b0c6w12_2_2 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6w12_2_2

@[expose] def wits_A7b0c6w12 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c6w12_0_0), (0, 1, w_A7b0c6w12_0_1), (0, 2, w_A7b0c6w12_0_2), (1, 0, w_A7b0c6w12_1_0), (1, 1, w_A7b0c6w12_1_1), (1, 2, w_A7b0c6w12_1_2), (2, 0, w_A7b0c6w12_2_0), (2, 1, w_A7b0c6w12_2_1), (2, 2, w_A7b0c6w12_2_2)]

theorem hwits_A7b0c6w12 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 6 (-1) (-2) wits_A7b0c6w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_0_0) (by rfl)]
      exact hcell_A7b0c6w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_0_1) (by rfl)]
      exact hcell_A7b0c6w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_0_2) (by rfl)]
      exact hcell_A7b0c6w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_1_0) (by rfl)]
      exact hcell_A7b0c6w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_1_1) (by rfl)]
      exact hcell_A7b0c6w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_1_2) (by rfl)]
      exact hcell_A7b0c6w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_2_0) (by rfl)]
      exact hcell_A7b0c6w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_2_1) (by rfl)]
      exact hcell_A7b0c6w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w12_2_2) (by rfl)]
      exact hcell_A7b0c6w12_2_2

@[expose] def w_A7b0c6w21_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w21.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w21_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w21_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w21_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w21_1_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0

@[expose] def w_A7b0c6w21_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1

@[expose] def w_A7b0c6w21_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b0c6w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b0c6w21_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1

@[expose] def w_A7b0c6w21_2_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6w21_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 1, 2, 0, 1, 2, 0, 1] [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6w21_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 1, 1, 1, 1, 1, 1, 1] [7, 0, 6, 7, 6, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6w21_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 1, 2, 0, 1, 2, 0, 1] [7, 0, 6, 7, 6, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b0c6w21_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 0 6 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 1, 1, 1, 1, 1, 1, 1] [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b0c6w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b0c6w21_0_0) = true := by
  rw [show w_A7b0c6w21_0_0 = .reuse ((GGResIShape.A7b0c6w21.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w21.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6w21.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b0c6w21_0_1) = true := by
  rw [show w_A7b0c6w21_0_1 = .reuse ((GGResIShape.A7b0c6w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b0c6w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b0c6w21_0_2) = true := by
  rw [show w_A7b0c6w21_0_2 = .reuse ((GGResIShape.A7b0c6w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b0c6w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b0c6w21_1_0) = true := by
  rw [show w_A7b0c6w21_1_0 = .reuse ((GGResIShape.A7b0c6w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b0c6w21_1_1) = true := by
  rw [show w_A7b0c6w21_1_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6w21_1_1

theorem hcell_A7b0c6w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b0c6w21_1_2) = true := by
  rw [show w_A7b0c6w21_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6w21_1_2

theorem hcell_A7b0c6w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b0c6w21_2_0) = true := by
  rw [show w_A7b0c6w21_2_0 = .reuse ((GGResIShape.A7b0c6w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b0c6w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b0c6w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b0c6w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b0c6w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b0c6w21_2_1) = true := by
  rw [show w_A7b0c6w21_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6w21_2_1

theorem hcell_A7b0c6w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 0 6 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b0c6w21_2_2) = true := by
  rw [show w_A7b0c6w21_2_2 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b0c6w21_2_2

@[expose] def wits_A7b0c6w21 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b0c6w21_0_0), (0, 1, w_A7b0c6w21_0_1), (0, 2, w_A7b0c6w21_0_2), (1, 0, w_A7b0c6w21_1_0), (1, 1, w_A7b0c6w21_1_1), (1, 2, w_A7b0c6w21_1_2), (2, 0, w_A7b0c6w21_2_0), (2, 1, w_A7b0c6w21_2_1), (2, 2, w_A7b0c6w21_2_2)]

theorem hwits_A7b0c6w21 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 6 (-2) (-1) wits_A7b0c6w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_0_0) (by rfl)]
      exact hcell_A7b0c6w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_0_1) (by rfl)]
      exact hcell_A7b0c6w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_0_2) (by rfl)]
      exact hcell_A7b0c6w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_1_0) (by rfl)]
      exact hcell_A7b0c6w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_1_1) (by rfl)]
      exact hcell_A7b0c6w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_1_2) (by rfl)]
      exact hcell_A7b0c6w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_2_0) (by rfl)]
      exact hcell_A7b0c6w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_2_1) (by rfl)]
      exact hcell_A7b0c6w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6w21_2_2) (by rfl)]
      exact hcell_A7b0c6w21_2_2

@[expose] def wits_A7_b0 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  if s = (1, -1, -2) then wits_A7b0c1w12
  else if s = (1, -2, -1) then wits_A7b0c1w21
  else if s = (2, -1, -1) then wits_A7b0c2
  else if s = (3, -1, -1) then wits_A7b0c3
  else if s = (4, -1, -1) then wits_A7b0c4
  else if s = (5, -1, -1) then wits_A7b0c5
  else if s = (6, -1, -1) then wits_A7b0c6
  else if s = (6, -1, -2) then wits_A7b0c6w12
  else if s = (6, -2, -1) then wits_A7b0c6w21
  else []

theorem cell_A7_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.A 7) 0 (GGResIDisp.A7.shapes_A7_b0) (wits_A7_b0) := by
  intro s hs
  simp only [GGResIDisp.A7.shapes_A7_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_A7_b0, if_pos rfl]
    exact hwits_A7b0c1w12
  · simp only [wits_A7_b0, if_neg (by decide : ¬ (((1, -2, -1)) = ((1, -1, -2)))), if_pos rfl]
    exact hwits_A7b0c1w21
  · simp only [wits_A7_b0, if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -2, -1)))), if_pos rfl]
    exact hwits_A7b0c2
  · simp only [wits_A7_b0, if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_A7b0c3
  · simp only [wits_A7_b0, if_neg (by decide : ¬ (((4, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_A7b0c4
  · simp only [wits_A7_b0, if_neg (by decide : ¬ (((5, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((4, -1, -1)))), if_pos rfl]
    exact hwits_A7b0c5
  · simp only [wits_A7_b0, if_neg (by decide : ¬ (((6, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((5, -1, -1)))), if_pos rfl]
    exact hwits_A7b0c6
  · simp only [wits_A7_b0, if_neg (by decide : ¬ (((6, -1, -2)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((5, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((6, -1, -1)))), if_pos rfl]
    exact hwits_A7b0c6w12
  · simp only [wits_A7_b0, if_neg (by decide : ¬ (((6, -2, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((5, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((6, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((6, -1, -2)))), if_pos rfl]
    exact hwits_A7b0c6w21
theorem hsideOK_A7_b0 :
    ∀ s ∈ GGResIDisp.A7.shapes_A7_b0, ∀ w ∈ wits_A7_b0 s,
      ggResQTwoCellSideOK (0 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.A7.shapes_A7_b0.all fun s => (wits_A7_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_A7_b0 :
    ∀ s ∈ GGResIDisp.A7.shapes_A7_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.A7.shapes_A7_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

@[expose] def w_A7b6c0_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0_1_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0

@[expose] def w_A7b6c0_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0

@[expose] def w_A7b6c0_2_2 : GGResQTwoCell 7 :=
  .commonKernel [1, 1, 1, 1, 1, 1, 1, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 1, 1, 1, 1, 1, 1, 1] [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 2, 1, 0, 2, 1, 0, 1] [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b6c0_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c0_0_0) = true := by
  rw [show w_A7b6c0_0_0 = .reuse ((GGResIShape.A7b6c0.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c0.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c0_0_1) = true := by
  rw [show w_A7b6c0_0_1 = .reuse ((GGResIShape.A7b6c0.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c0.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c0_0_2) = true := by
  rw [show w_A7b6c0_0_2 = .reuse ((GGResIShape.A7b6c0.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c0.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c0.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c0_1_0) = true := by
  rw [show w_A7b6c0_1_0 = .reuse ((GGResIShape.A7b6c0.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c0.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c0_1_1) = true := by
  rw [show w_A7b6c0_1_1 = .reuse ((GGResIShape.A7b6c0.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c0.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c0.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c0_1_2) = true := by
  rw [show w_A7b6c0_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0_1_2

theorem hcell_A7b6c0_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c0_2_0) = true := by
  rw [show w_A7b6c0_2_0 = .reuse ((GGResIShape.A7b6c0.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c0.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c0.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c0_2_1) = true := by
  rw [show w_A7b6c0_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 6, 5, 7, 0, 6, 7, 6, 0, 7, 5, 6, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0_2_1

theorem hcell_A7b6c0_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c0_2_2) = true := by
  rw [show w_A7b6c0_2_2 = .commonKernel [1, 1, 1, 1, 1, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 1, 1, 1, 1]) (by decide +kernel)

@[expose] def wits_A7b6c0 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c0_0_0), (0, 1, w_A7b6c0_0_1), (0, 2, w_A7b6c0_0_2), (1, 0, w_A7b6c0_1_0), (1, 1, w_A7b6c0_1_1), (1, 2, w_A7b6c0_1_2), (2, 0, w_A7b6c0_2_0), (2, 1, w_A7b6c0_2_1), (2, 2, w_A7b6c0_2_2)]

theorem hwits_A7b6c0 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 0 (-1) (-1) wits_A7b6c0 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_0_0) (by rfl)]
      exact hcell_A7b6c0_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_0_1) (by rfl)]
      exact hcell_A7b6c0_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_0_2) (by rfl)]
      exact hcell_A7b6c0_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_1_0) (by rfl)]
      exact hcell_A7b6c0_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_1_1) (by rfl)]
      exact hcell_A7b6c0_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_1_2) (by rfl)]
      exact hcell_A7b6c0_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_2_0) (by rfl)]
      exact hcell_A7b6c0_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_2_1) (by rfl)]
      exact hcell_A7b6c0_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0_2_2) (by rfl)]
      exact hcell_A7b6c0_2_2

@[expose] def w_A7b6c0w12_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0w12.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0w12_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0w12_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0w12_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0w12_1_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2

@[expose] def w_A7b6c0w12_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1

@[expose] def w_A7b6c0w12_2_0 : GGResQTwoCell 7 :=
  .commonKernel [1, 0, 2, 1, 0, 2, 1, 1]

@[expose] def w_A7b6c0w12_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1

@[expose] def w_A7b6c0w12_2_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0w12_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 2, 2, 2, 2, 2, 2, 1] [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0w12_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 1, 2, 0, 1, 2, 0, 1] [7, 0, 6, 7, 6, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0w12_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 2, 2, 2, 2, 2, 2, 1] [7, 0, 6, 7, 6, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0w12_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 1, 2, 0, 1, 2, 0, 1] [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b6c0w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c0w12_0_0) = true := by
  rw [show w_A7b6c0w12_0_0 = .reuse ((GGResIShape.A7b6c0w12.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0w12.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c0w12.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c0w12_0_1) = true := by
  rw [show w_A7b6c0w12_0_1 = .reuse ((GGResIShape.A7b6c0w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c0w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c0w12_0_2) = true := by
  rw [show w_A7b6c0w12_0_2 = .reuse ((GGResIShape.A7b6c0w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c0w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c0w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c0w12_1_0) = true := by
  rw [show w_A7b6c0w12_1_0 = .reuse ((GGResIShape.A7b6c0w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c0w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c0w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c0w12_1_1) = true := by
  rw [show w_A7b6c0w12_1_1 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0w12_1_1

theorem hcell_A7b6c0w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c0w12_1_2) = true := by
  rw [show w_A7b6c0w12_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0w12_1_2

theorem hcell_A7b6c0w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c0w12_2_0) = true := by
  rw [show w_A7b6c0w12_2_0 = .commonKernel [1, 0, 2, 1, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 0, 2, 1, 0, 2, 1, 1]) (by decide +kernel)

theorem hcell_A7b6c0w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c0w12_2_1) = true := by
  rw [show w_A7b6c0w12_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0w12_2_1

theorem hcell_A7b6c0w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c0w12_2_2) = true := by
  rw [show w_A7b6c0w12_2_2 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0w12_2_2

@[expose] def wits_A7b6c0w12 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c0w12_0_0), (0, 1, w_A7b6c0w12_0_1), (0, 2, w_A7b6c0w12_0_2), (1, 0, w_A7b6c0w12_1_0), (1, 1, w_A7b6c0w12_1_1), (1, 2, w_A7b6c0w12_1_2), (2, 0, w_A7b6c0w12_2_0), (2, 1, w_A7b6c0w12_2_1), (2, 2, w_A7b6c0w12_2_2)]

theorem hwits_A7b6c0w12 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 0 (-1) (-2) wits_A7b6c0w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_0_0) (by rfl)]
      exact hcell_A7b6c0w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_0_1) (by rfl)]
      exact hcell_A7b6c0w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_0_2) (by rfl)]
      exact hcell_A7b6c0w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_1_0) (by rfl)]
      exact hcell_A7b6c0w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_1_1) (by rfl)]
      exact hcell_A7b6c0w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_1_2) (by rfl)]
      exact hcell_A7b6c0w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_2_0) (by rfl)]
      exact hcell_A7b6c0w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_2_1) (by rfl)]
      exact hcell_A7b6c0w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w12_2_2) (by rfl)]
      exact hcell_A7b6c0w12_2_2

@[expose] def w_A7b6c0w21_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0w21.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0w21_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0w21_0_2 : GGResQTwoCell 7 :=
  .commonKernel [1, 1, 1, 1, 1, 1, 1, 1]

@[expose] def w_A7b6c0w21_1_0 : GGResQTwoCell 7 :=
  .commonKernel [2, 0, 1, 2, 0, 1, 2, 1]

@[expose] def w_A7b6c0w21_1_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2

@[expose] def w_A7b6c0w21_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1

@[expose] def w_A7b6c0w21_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c0w21_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1

@[expose] def w_A7b6c0w21_2_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0w21_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 2, 1, 0, 2, 1, 0, 1] [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0w21_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 1, 1, 1, 1, 1, 1, 1] [7, 0, 6, 7, 6, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0w21_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 2, 1, 0, 2, 1, 0, 1] [7, 0, 6, 7, 6, 0, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c0w21_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 1, 1, 1, 1, 1, 1, 1] [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b6c0w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c0w21_0_0) = true := by
  rw [show w_A7b6c0w21_0_0 = .reuse ((GGResIShape.A7b6c0w21.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0w21.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c0w21.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c0w21_0_1) = true := by
  rw [show w_A7b6c0w21_0_1 = .reuse ((GGResIShape.A7b6c0w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c0w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c0w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c0w21_0_2) = true := by
  rw [show w_A7b6c0w21_0_2 = .commonKernel [1, 1, 1, 1, 1, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 1, 1, 1, 1, 1, 1, 1]) (by decide +kernel)

theorem hcell_A7b6c0w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c0w21_1_0) = true := by
  rw [show w_A7b6c0w21_1_0 = .commonKernel [2, 0, 1, 2, 0, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 1, 2, 0, 1, 2, 1]) (by decide +kernel)

theorem hcell_A7b6c0w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c0w21_1_1) = true := by
  rw [show w_A7b6c0w21_1_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0w21_1_1

theorem hcell_A7b6c0w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c0w21_1_2) = true := by
  rw [show w_A7b6c0w21_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0w21_1_2

theorem hcell_A7b6c0w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c0w21_2_0) = true := by
  rw [show w_A7b6c0w21_2_0 = .reuse ((GGResIShape.A7b6c0w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c0w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c0w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c0w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c0w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c0w21_2_1) = true := by
  rw [show w_A7b6c0w21_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 2, 1, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 0, 6, 7, 6, 0, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0w21_2_1

theorem hcell_A7b6c0w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 0 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c0w21_2_2) = true := by
  rw [show w_A7b6c0w21_2_2 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 1, 1, 1, 1, 1, 1, 1] Rq2_0777788aee31d1c4 [7, 0, 1, 7, 0, 6, 7, 6, 0, 7, 1, 0, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c0w21_2_2

@[expose] def wits_A7b6c0w21 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c0w21_0_0), (0, 1, w_A7b6c0w21_0_1), (0, 2, w_A7b6c0w21_0_2), (1, 0, w_A7b6c0w21_1_0), (1, 1, w_A7b6c0w21_1_1), (1, 2, w_A7b6c0w21_1_2), (2, 0, w_A7b6c0w21_2_0), (2, 1, w_A7b6c0w21_2_1), (2, 2, w_A7b6c0w21_2_2)]

theorem hwits_A7b6c0w21 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 0 (-2) (-1) wits_A7b6c0w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_0_0) (by rfl)]
      exact hcell_A7b6c0w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_0_1) (by rfl)]
      exact hcell_A7b6c0w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_0_2) (by rfl)]
      exact hcell_A7b6c0w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_1_0) (by rfl)]
      exact hcell_A7b6c0w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_1_1) (by rfl)]
      exact hcell_A7b6c0w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_1_2) (by rfl)]
      exact hcell_A7b6c0w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_2_0) (by rfl)]
      exact hcell_A7b6c0w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_2_1) (by rfl)]
      exact hcell_A7b6c0w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c0w21_2_2) (by rfl)]
      exact hcell_A7b6c0w21_2_2

@[expose] def w_A7b6c1_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c1.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c1_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c1.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c1_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c1.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c1_1_0 : GGResQTwoCell 7 :=
  .commonKernel [0, 0, 2, 1, 0, 2, 1, 1]

@[expose] def w_A7b6c1_1_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 2, 3, 6, 5, 7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7, 5, 6, 3, 2, 1, 7] 0

@[expose] def w_A7b6c1_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7] 1

@[expose] def w_A7b6c1_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c1.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c1_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7] 1

@[expose] def w_A7b6c1_2_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 1, 7] 0

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c1_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 1 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 2, 2, 2, 2, 2, 2, 1] [7, 1, 2, 3, 6, 5, 7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7, 5, 6, 3, 2, 1, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c1_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 1 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 1, 2, 0, 1, 2, 0, 1] [7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c1_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 1 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 2, 2, 2, 2, 2, 2, 1] [7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7] 1 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c1_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 1, 2, 0, 1, 2, 0, 1] [7, 1, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 1, 7] 0 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b6c1_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c1_0_0) = true := by
  rw [show w_A7b6c1_0_0 = .reuse ((GGResIShape.A7b6c1.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c1.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c1.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c1_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c1_0_1) = true := by
  rw [show w_A7b6c1_0_1 = .reuse ((GGResIShape.A7b6c1.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c1.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c1.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c1_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c1_0_2) = true := by
  rw [show w_A7b6c1_0_2 = .reuse ((GGResIShape.A7b6c1.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c1.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c1.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c1.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c1_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c1_1_0) = true := by
  rw [show w_A7b6c1_1_0 = .commonKernel [0, 0, 2, 1, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 2, 1, 0, 2, 1, 1]) (by decide +kernel)

theorem hcell_A7b6c1_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c1_1_1) = true := by
  rw [show w_A7b6c1_1_1 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 2, 3, 6, 5, 7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7, 5, 6, 3, 2, 1, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 2, 3, 6, 5, 7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7, 5, 6, 3, 2, 1, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c1_1_1

theorem hcell_A7b6c1_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c1_1_2) = true := by
  rw [show w_A7b6c1_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c1_1_2

theorem hcell_A7b6c1_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c1_2_0) = true := by
  rw [show w_A7b6c1_2_0 = .reuse ((GGResIShape.A7b6c1.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c1.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c1.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c1.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c1_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c1_2_1) = true := by
  rw [show w_A7b6c1_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7] 1 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 2, 2, 2, 2, 2, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 6, 7, 6, 1, 2, 0, 1, 7] 1) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c1_2_1

theorem hcell_A7b6c1_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 1 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c1_2_2) = true := by
  rw [show w_A7b6c1_2_2 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 1, 7] 0 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 2, 0, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 1, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 1, 7] 0) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c1_2_2

@[expose] def wits_A7b6c1 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c1_0_0), (0, 1, w_A7b6c1_0_1), (0, 2, w_A7b6c1_0_2), (1, 0, w_A7b6c1_1_0), (1, 1, w_A7b6c1_1_1), (1, 2, w_A7b6c1_1_2), (2, 0, w_A7b6c1_2_0), (2, 1, w_A7b6c1_2_1), (2, 2, w_A7b6c1_2_2)]

theorem hwits_A7b6c1 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 1 (-1) (-1) wits_A7b6c1 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_0_0) (by rfl)]
      exact hcell_A7b6c1_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_0_1) (by rfl)]
      exact hcell_A7b6c1_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_0_2) (by rfl)]
      exact hcell_A7b6c1_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_1_0) (by rfl)]
      exact hcell_A7b6c1_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_1_1) (by rfl)]
      exact hcell_A7b6c1_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_1_2) (by rfl)]
      exact hcell_A7b6c1_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_2_0) (by rfl)]
      exact hcell_A7b6c1_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_2_1) (by rfl)]
      exact hcell_A7b6c1_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c1_2_2) (by rfl)]
      exact hcell_A7b6c1_2_2

@[expose] def w_A7b6c2_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c2.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c2_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c2.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c2_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c2.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c2_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c2.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c2_1_1 : GGResQTwoCell 7 :=
  .commonKernel [2, 1, 0, 1, 2, 0, 1, 1]

@[expose] def w_A7b6c2_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c2.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c2_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c2.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c2_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c2.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c2_2_2 : GGResQTwoCell 7 :=
  .commonKernel [0, 0, 0, 2, 1, 0, 2, 1]

theorem hcell_A7b6c2_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c2_0_0) = true := by
  rw [show w_A7b6c2_0_0 = .reuse ((GGResIShape.A7b6c2.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c2.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c2.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c2_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c2_0_1) = true := by
  rw [show w_A7b6c2_0_1 = .reuse ((GGResIShape.A7b6c2.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c2.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c2.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c2_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c2_0_2) = true := by
  rw [show w_A7b6c2_0_2 = .reuse ((GGResIShape.A7b6c2.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c2.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c2.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c2.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c2_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c2_1_0) = true := by
  rw [show w_A7b6c2_1_0 = .reuse ((GGResIShape.A7b6c2.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c2.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c2.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c2_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c2_1_1) = true := by
  rw [show w_A7b6c2_1_1 = .commonKernel [2, 1, 0, 1, 2, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 1, 2, 0, 1, 1]) (by decide +kernel)

theorem hcell_A7b6c2_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c2_1_2) = true := by
  rw [show w_A7b6c2_1_2 = .reuse ((GGResIShape.A7b6c2.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c2.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c2.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c2.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c2_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c2_2_0) = true := by
  rw [show w_A7b6c2_2_0 = .reuse ((GGResIShape.A7b6c2.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c2.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c2.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c2_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c2_2_1) = true := by
  rw [show w_A7b6c2_2_1 = .reuse ((GGResIShape.A7b6c2.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c2.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c2.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c2.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c2_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 2 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c2_2_2) = true := by
  rw [show w_A7b6c2_2_2 = .commonKernel [0, 0, 0, 2, 1, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 2, 1, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_A7b6c2 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c2_0_0), (0, 1, w_A7b6c2_0_1), (0, 2, w_A7b6c2_0_2), (1, 0, w_A7b6c2_1_0), (1, 1, w_A7b6c2_1_1), (1, 2, w_A7b6c2_1_2), (2, 0, w_A7b6c2_2_0), (2, 1, w_A7b6c2_2_1), (2, 2, w_A7b6c2_2_2)]

theorem hwits_A7b6c2 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 2 (-1) (-1) wits_A7b6c2 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_0_0) (by rfl)]
      exact hcell_A7b6c2_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_0_1) (by rfl)]
      exact hcell_A7b6c2_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_0_2) (by rfl)]
      exact hcell_A7b6c2_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_1_0) (by rfl)]
      exact hcell_A7b6c2_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_1_1) (by rfl)]
      exact hcell_A7b6c2_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_1_2) (by rfl)]
      exact hcell_A7b6c2_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_2_0) (by rfl)]
      exact hcell_A7b6c2_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_2_1) (by rfl)]
      exact hcell_A7b6c2_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c2_2_2) (by rfl)]
      exact hcell_A7b6c2_2_2

@[expose] def w_A7b6c3_0_0 : GGResQTwoCell 7 :=
  .commonKernel [2, 1, 0, 2, 0, 1, 2, 1]

@[expose] def w_A7b6c3_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c3.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c3_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c3.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c3_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c3.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c3_1_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 3, 2, 1, 0, 4, 3, 2, 1, 7, 3, 2, 4, 3, 6, 7, 6, 3, 4, 2, 3, 7, 1, 2, 3, 4, 0, 1, 2, 3, 7] 5

@[expose] def w_A7b6c3_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c3.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c3_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c3.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c3_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c3.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c3_2_2 : GGResQTwoCell 7 :=
  .commonKernel [1, 2, 0, 1, 1, 1, 1, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c3_1_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 0, 0, 0, 2, 1, 0, 1] [7, 3, 2, 1, 0, 4, 3, 2, 1, 7, 3, 2, 4, 3, 6, 7, 6, 3, 4, 2, 3, 7, 1, 2, 3, 4, 0, 1, 2, 3, 7] 5 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b6c3_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c3_0_0) = true := by
  rw [show w_A7b6c3_0_0 = .commonKernel [2, 1, 0, 2, 0, 1, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 1, 0, 2, 0, 1, 2, 1]) (by decide +kernel)

theorem hcell_A7b6c3_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c3_0_1) = true := by
  rw [show w_A7b6c3_0_1 = .reuse ((GGResIShape.A7b6c3.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c3.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c3.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c3_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c3_0_2) = true := by
  rw [show w_A7b6c3_0_2 = .reuse ((GGResIShape.A7b6c3.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c3.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c3.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c3.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c3_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c3_1_0) = true := by
  rw [show w_A7b6c3_1_0 = .reuse ((GGResIShape.A7b6c3.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c3.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c3.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c3_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c3_1_1) = true := by
  rw [show w_A7b6c3_1_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 3, 2, 1, 0, 4, 3, 2, 1, 7, 3, 2, 4, 3, 6, 7, 6, 3, 4, 2, 3, 7, 1, 2, 3, 4, 0, 1, 2, 3, 7] 5 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 2, 1, 0, 1] Rq2_0777788aee31d1c4 [7, 3, 2, 1, 0, 4, 3, 2, 1, 7, 3, 2, 4, 3, 6, 7, 6, 3, 4, 2, 3, 7, 1, 2, 3, 4, 0, 1, 2, 3, 7] 5) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c3_1_1

theorem hcell_A7b6c3_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c3_1_2) = true := by
  rw [show w_A7b6c3_1_2 = .reuse ((GGResIShape.A7b6c3.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c3.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c3.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c3.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c3_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c3_2_0) = true := by
  rw [show w_A7b6c3_2_0 = .reuse ((GGResIShape.A7b6c3.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c3.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c3.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c3_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c3_2_1) = true := by
  rw [show w_A7b6c3_2_1 = .reuse ((GGResIShape.A7b6c3.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c3.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c3.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c3.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c3_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 3 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c3_2_2) = true := by
  rw [show w_A7b6c3_2_2 = .commonKernel [1, 2, 0, 1, 1, 1, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [1, 2, 0, 1, 1, 1, 1, 1]) (by decide +kernel)

@[expose] def wits_A7b6c3 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c3_0_0), (0, 1, w_A7b6c3_0_1), (0, 2, w_A7b6c3_0_2), (1, 0, w_A7b6c3_1_0), (1, 1, w_A7b6c3_1_1), (1, 2, w_A7b6c3_1_2), (2, 0, w_A7b6c3_2_0), (2, 1, w_A7b6c3_2_1), (2, 2, w_A7b6c3_2_2)]

theorem hwits_A7b6c3 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 3 (-1) (-1) wits_A7b6c3 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_0_0) (by rfl)]
      exact hcell_A7b6c3_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_0_1) (by rfl)]
      exact hcell_A7b6c3_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_0_2) (by rfl)]
      exact hcell_A7b6c3_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_1_0) (by rfl)]
      exact hcell_A7b6c3_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_1_1) (by rfl)]
      exact hcell_A7b6c3_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_1_2) (by rfl)]
      exact hcell_A7b6c3_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_2_0) (by rfl)]
      exact hcell_A7b6c3_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_2_1) (by rfl)]
      exact hcell_A7b6c3_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c3_2_2) (by rfl)]
      exact hcell_A7b6c3_2_2

@[expose] def w_A7b6c4_0_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c4.cell3.getD 0 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c4_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c4.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c4_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c4.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c4_1_0 : GGResQTwoCell 7 :=
  .commonKernel [0, 0, 0, 0, 0, 2, 1, 1]

@[expose] def w_A7b6c4_1_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c4.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c4_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c4.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c4_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c4.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c4_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c4.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c4_2_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 4, 3, 5, 4, 6, 7, 6, 4, 5, 3, 4, 7] 2

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c4_2_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 4 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 1, 0, 2, 1, 2, 0, 1] [7, 4, 3, 5, 4, 6, 7, 6, 4, 5, 3, 4, 7] 2 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b6c4_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c4_0_0) = true := by
  rw [show w_A7b6c4_0_0 = .reuse ((GGResIShape.A7b6c4.cell3.getD 0 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c4.hcell3 (0 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c4.cell3.getD 0 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c4_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c4_0_1) = true := by
  rw [show w_A7b6c4_0_1 = .reuse ((GGResIShape.A7b6c4.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c4.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c4.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c4_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c4_0_2) = true := by
  rw [show w_A7b6c4_0_2 = .reuse ((GGResIShape.A7b6c4.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c4.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c4.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c4.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c4_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c4_1_0) = true := by
  rw [show w_A7b6c4_1_0 = .commonKernel [0, 0, 0, 0, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 0, 0, 2, 1, 1]) (by decide +kernel)

theorem hcell_A7b6c4_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c4_1_1) = true := by
  rw [show w_A7b6c4_1_1 = .reuse ((GGResIShape.A7b6c4.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c4.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c4.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c4_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c4_1_2) = true := by
  rw [show w_A7b6c4_1_2 = .reuse ((GGResIShape.A7b6c4.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c4.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c4.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c4.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c4_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c4_2_0) = true := by
  rw [show w_A7b6c4_2_0 = .reuse ((GGResIShape.A7b6c4.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c4.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c4.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c4_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c4_2_1) = true := by
  rw [show w_A7b6c4_2_1 = .reuse ((GGResIShape.A7b6c4.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c4.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c4.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c4.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c4_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 4 (-1) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c4_2_2) = true := by
  rw [show w_A7b6c4_2_2 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 4, 3, 5, 4, 6, 7, 6, 4, 5, 3, 4, 7] 2 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 2, 0, 1] Rq2_0777788aee31d1c4 [7, 4, 3, 5, 4, 6, 7, 6, 4, 5, 3, 4, 7] 2) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c4_2_2

@[expose] def wits_A7b6c4 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c4_0_0), (0, 1, w_A7b6c4_0_1), (0, 2, w_A7b6c4_0_2), (1, 0, w_A7b6c4_1_0), (1, 1, w_A7b6c4_1_1), (1, 2, w_A7b6c4_1_2), (2, 0, w_A7b6c4_2_0), (2, 1, w_A7b6c4_2_1), (2, 2, w_A7b6c4_2_2)]

theorem hwits_A7b6c4 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 4 (-1) (-1) wits_A7b6c4 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_0_0) (by rfl)]
      exact hcell_A7b6c4_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_0_1) (by rfl)]
      exact hcell_A7b6c4_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_0_2) (by rfl)]
      exact hcell_A7b6c4_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_1_0) (by rfl)]
      exact hcell_A7b6c4_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_1_1) (by rfl)]
      exact hcell_A7b6c4_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_1_2) (by rfl)]
      exact hcell_A7b6c4_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_2_0) (by rfl)]
      exact hcell_A7b6c4_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_2_1) (by rfl)]
      exact hcell_A7b6c4_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c4_2_2) (by rfl)]
      exact hcell_A7b6c4_2_2

@[expose] def w_A7b6c5w12_0_0 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3

@[expose] def w_A7b6c5w12_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w12.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w12_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w12.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w12_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w12.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w12_1_1 : GGResQTwoCell 7 :=
  .commonKernel [0, 0, 0, 0, 0, 0, 1, 1]

@[expose] def w_A7b6c5w12_1_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w12.cell3.getD 5 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w12_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w12.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w12_2_1 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 0, 0, 1, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3

@[expose] def w_A7b6c5w12_2_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w12.cell3.getD 8 (0, 0, .o2b)).2.2)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c5w12_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 5 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [2, 1, 0, 2, 1, 0, 0, 1] [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c5w12_2_1 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 5 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 0, 0, 0, 0, 0, 1, 1] [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b6c5w12_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c5w12_0_0) = true := by
  rw [show w_A7b6c5w12_0_0 = .norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [2, 1, 0, 2, 1, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c5w12_0_0

theorem hcell_A7b6c5w12_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c5w12_0_1) = true := by
  rw [show w_A7b6c5w12_0_1 = .reuse ((GGResIShape.A7b6c5w12.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w12.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c5w12.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w12_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c5w12_0_2) = true := by
  rw [show w_A7b6c5w12_0_2 = .reuse ((GGResIShape.A7b6c5w12.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w12.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w12.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c5w12.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w12_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c5w12_1_0) = true := by
  rw [show w_A7b6c5w12_1_0 = .reuse ((GGResIShape.A7b6c5w12.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w12.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c5w12.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w12_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c5w12_1_1) = true := by
  rw [show w_A7b6c5w12_1_1 = .commonKernel [0, 0, 0, 0, 0, 0, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 0, 0, 0, 1, 1]) (by decide +kernel)

theorem hcell_A7b6c5w12_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c5w12_1_2) = true := by
  rw [show w_A7b6c5w12_1_2 = .reuse ((GGResIShape.A7b6c5w12.cell3.getD 5 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w12.hcell3 (1 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w12.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c5w12.cell3.getD 5 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w12_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c5w12_2_0) = true := by
  rw [show w_A7b6c5w12_2_0 = .reuse ((GGResIShape.A7b6c5w12.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w12.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c5w12.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w12_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c5w12_2_1) = true := by
  rw [show w_A7b6c5w12_2_1 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 0, 0, 1, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 0, 0, 1, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c5w12_2_1

theorem hcell_A7b6c5w12_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-1) (-2) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c5w12_2_2) = true := by
  rw [show w_A7b6c5w12_2_2 = .reuse ((GGResIShape.A7b6c5w12.cell3.getD 8 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w12.hcell3 (2 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w12.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c5w12.cell3.getD 8 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

@[expose] def wits_A7b6c5w12 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c5w12_0_0), (0, 1, w_A7b6c5w12_0_1), (0, 2, w_A7b6c5w12_0_2), (1, 0, w_A7b6c5w12_1_0), (1, 1, w_A7b6c5w12_1_1), (1, 2, w_A7b6c5w12_1_2), (2, 0, w_A7b6c5w12_2_0), (2, 1, w_A7b6c5w12_2_1), (2, 2, w_A7b6c5w12_2_2)]

theorem hwits_A7b6c5w12 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 5 (-1) (-2) wits_A7b6c5w12 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_0_0) (by rfl)]
      exact hcell_A7b6c5w12_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_0_1) (by rfl)]
      exact hcell_A7b6c5w12_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_0_2) (by rfl)]
      exact hcell_A7b6c5w12_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_1_0) (by rfl)]
      exact hcell_A7b6c5w12_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_1_1) (by rfl)]
      exact hcell_A7b6c5w12_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_1_2) (by rfl)]
      exact hcell_A7b6c5w12_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_2_0) (by rfl)]
      exact hcell_A7b6c5w12_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_2_1) (by rfl)]
      exact hcell_A7b6c5w12_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w12_2_2) (by rfl)]
      exact hcell_A7b6c5w12_2_2

@[expose] def w_A7b6c5w21_0_0 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 0, 1, 2, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3

@[expose] def w_A7b6c5w21_0_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w21.cell3.getD 1 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w21_0_2 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w21.cell3.getD 2 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w21_1_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w21.cell3.getD 3 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w21_1_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w21.cell3.getD 4 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w21_1_2 : GGResQTwoCell 7 :=
  .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 0, 0, 2, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3

@[expose] def w_A7b6c5w21_2_0 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w21.cell3.getD 6 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w21_2_1 : GGResQTwoCell 7 :=
  .reuse ((GGResIShape.A7b6c5w21.cell3.getD 7 (0, 0, .o2b)).2.2)

@[expose] def w_A7b6c5w21_2_2 : GGResQTwoCell 7 :=
  .commonKernel [0, 0, 0, 0, 0, 0, 2, 1]

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c5w21_0_0 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 5 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [1, 2, 0, 1, 2, 0, 0, 1] [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

open scoped CFSG.Decide.Bounded in
theorem hnorm_A7b6c5w21_1_2 :
    GGResQTwoNormOKK (ggStdTableI (Int.cast) (CartanMatrix.A 7) 6 5 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3))
      [0, 1, 2, 3, 4, 5, 6] Rq2_0777788aee31d1c4 [0, 0, 0, 0, 0, 0, 2, 1] [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3 := by
  exact GGResQTwoPacked.GGResQTwoNormOKK_of_pk (D := pkDataA7) (by decide +kernel)
    (by decide +kernel) (pkListA7 _ _ _ _ _ _) (by decide) (by decide +kernel) (by decide +kernel)

theorem hcell_A7b6c5w21_0_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (0 : ZMod 3) (0 : ZMod 3) (w_A7b6c5w21_0_0) = true := by
  rw [show w_A7b6c5w21_0_0 = .norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 0, 1, 2, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [1, 2, 0, 1, 2, 0, 0, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c5w21_0_0

theorem hcell_A7b6c5w21_0_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (0 : ZMod 3) (1 : ZMod 3) (w_A7b6c5w21_0_1) = true := by
  rw [show w_A7b6c5w21_0_1 = .reuse ((GGResIShape.A7b6c5w21.cell3.getD 1 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w21.hcell3 (0 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c5w21.cell3.getD 1 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w21_0_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (0 : ZMod 3) (2 : ZMod 3) (w_A7b6c5w21_0_2) = true := by
  rw [show w_A7b6c5w21_0_2 = .reuse ((GGResIShape.A7b6c5w21.cell3.getD 2 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w21.hcell3 (0 : ZMod 3) (2 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w21.cell3.find?
        (fun w => w.1 == (0 : ZMod 3).val && w.2.1 == (2 : ZMod 3).val) =
        some ((0 : ZMod 3).val, (2 : ZMod 3).val,
          ((GGResIShape.A7b6c5w21.cell3.getD 2 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w21_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A7b6c5w21_1_0) = true := by
  rw [show w_A7b6c5w21_1_0 = .reuse ((GGResIShape.A7b6c5w21.cell3.getD 3 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w21.hcell3 (1 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c5w21.cell3.getD 3 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w21_1_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (1 : ZMod 3) (1 : ZMod 3) (w_A7b6c5w21_1_1) = true := by
  rw [show w_A7b6c5w21_1_1 = .reuse ((GGResIShape.A7b6c5w21.cell3.getD 4 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w21.hcell3 (1 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w21.cell3.find?
        (fun w => w.1 == (1 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((1 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c5w21.cell3.getD 4 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w21_1_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (1 : ZMod 3) (2 : ZMod 3) (w_A7b6c5w21_1_2) = true := by
  rw [show w_A7b6c5w21_1_2 = .norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 0, 0, 2, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3 from rfl]
  refine ggResQTwoCellCheckK_imp (.norm [0, 1, 2, 3, 4, 5, 6] [0, 0, 0, 0, 0, 0, 2, 1] Rq2_0777788aee31d1c4 [7, 5, 4, 6, 5, 7, 5, 6, 4, 5, 7] 3) ?_
  simpa [ggResQTwoCellCheckK] using decide_eq_true hnorm_A7b6c5w21_1_2

theorem hcell_A7b6c5w21_2_0 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (2 : ZMod 3) (0 : ZMod 3) (w_A7b6c5w21_2_0) = true := by
  rw [show w_A7b6c5w21_2_0 = .reuse ((GGResIShape.A7b6c5w21.cell3.getD 6 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w21.hcell3 (2 : ZMod 3) (0 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (0 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (0 : ZMod 3).val,
          ((GGResIShape.A7b6c5w21.cell3.getD 6 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w21_2_1 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (2 : ZMod 3) (1 : ZMod 3) (w_A7b6c5w21_2_1) = true := by
  rw [show w_A7b6c5w21_2_1 = .reuse ((GGResIShape.A7b6c5w21.cell3.getD 7 (0, 0, .o2b)).2.2) from rfl]
  refine ggResQTwoCellCheck_reuse_of_cellCheck ?_ ?_
  · decide
  · have h := GGResIShape.A7b6c5w21.hcell3 (2 : ZMod 3) (1 : ZMod 3)
    have hfind : GGResIShape.A7b6c5w21.cell3.find?
        (fun w => w.1 == (2 : ZMod 3).val && w.2.1 == (1 : ZMod 3).val) =
        some ((2 : ZMod 3).val, (1 : ZMod 3).val,
          ((GGResIShape.A7b6c5w21.cell3.getD 7 (0, 0, .o2b)).2.2)) := by rfl
    rw [ggCellAtI, hfind] at h
    exact h

theorem hcell_A7b6c5w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 7) 6 5 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A7b6c5w21_2_2) = true := by
  rw [show w_A7b6c5w21_2_2 = .commonKernel [0, 0, 0, 0, 0, 0, 2, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 0, 0, 0, 0, 2, 1]) (by decide +kernel)

@[expose] def wits_A7b6c5w21 : List (ℕ × ℕ × GGResQTwoCell 7) :=
  [(0, 0, w_A7b6c5w21_0_0), (0, 1, w_A7b6c5w21_0_1), (0, 2, w_A7b6c5w21_0_2), (1, 0, w_A7b6c5w21_1_0), (1, 1, w_A7b6c5w21_1_1), (1, 2, w_A7b6c5w21_1_2), (2, 0, w_A7b6c5w21_2_0), (2, 1, w_A7b6c5w21_2_1), (2, 2, w_A7b6c5w21_2_2)]

theorem hwits_A7b6c5w21 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 6 5 (-2) (-1) wits_A7b6c5w21 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_0_0) (by rfl)]
      exact hcell_A7b6c5w21_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_0_1) (by rfl)]
      exact hcell_A7b6c5w21_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_0_2) (by rfl)]
      exact hcell_A7b6c5w21_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_1_0) (by rfl)]
      exact hcell_A7b6c5w21_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_1_1) (by rfl)]
      exact hcell_A7b6c5w21_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_1_2) (by rfl)]
      exact hcell_A7b6c5w21_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_2_0) (by rfl)]
      exact hcell_A7b6c5w21_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_2_1) (by rfl)]
      exact hcell_A7b6c5w21_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b6c5w21_2_2) (by rfl)]
      exact hcell_A7b6c5w21_2_2

@[expose] def wits_A7_b6 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  if s = (0, -1, -1) then wits_A7b6c0
  else if s = (0, -1, -2) then wits_A7b6c0w12
  else if s = (0, -2, -1) then wits_A7b6c0w21
  else if s = (1, -1, -1) then wits_A7b6c1
  else if s = (2, -1, -1) then wits_A7b6c2
  else if s = (3, -1, -1) then wits_A7b6c3
  else if s = (4, -1, -1) then wits_A7b6c4
  else if s = (5, -1, -2) then wits_A7b6c5w12
  else if s = (5, -2, -1) then wits_A7b6c5w21
  else []

theorem cell_A7_b6 :
    GGResQTwoShapeCoverage (CartanMatrix.A 7) 6 (GGResIDisp.A7.shapes_A7_b6) (wits_A7_b6) := by
  intro s hs
  simp only [GGResIDisp.A7.shapes_A7_b6, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_A7_b6, if_pos rfl]
    exact hwits_A7b6c0
  · simp only [wits_A7_b6, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_A7b6c0w12
  · simp only [wits_A7_b6, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_A7b6c0w21
  · simp only [wits_A7_b6, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_A7b6c1
  · simp only [wits_A7_b6, if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_A7b6c2
  · simp only [wits_A7_b6, if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_A7b6c3
  · simp only [wits_A7_b6, if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_A7b6c4
  · simp only [wits_A7_b6, if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((4, -1, -1)))), if_pos rfl]
    exact hwits_A7b6c5w12
  · simp only [wits_A7_b6, if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((5, -1, -2)))), if_pos rfl]
    exact hwits_A7b6c5w21
theorem hsideOK_A7_b6 :
    ∀ s ∈ GGResIDisp.A7.shapes_A7_b6, ∀ w ∈ wits_A7_b6 s,
      ggResQTwoCellSideOK (6 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.A7.shapes_A7_b6.all fun s => (wits_A7_b6 s).all fun w =>
      ggResQTwoCellSideOKB (6 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_A7_b6 :
    ∀ s ∈ GGResIDisp.A7.shapes_A7_b6, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.A7.shapes_A7_b6.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataA7
