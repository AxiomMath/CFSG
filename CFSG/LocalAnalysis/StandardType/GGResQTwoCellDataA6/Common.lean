module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataA6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_2cce17e5c6cf7fa5 : List (Fin 7 × List (Fin 7)) :=
[(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (0, [1]), (1, [2]), (2, [3]), (3, [4]), (4, [5]), (0, [2, 1]), (1, [3, 2]), (2, [4, 3]), (3, [5, 4]), (0, [3, 2, 1]), (1, [4, 3, 2]), (2, [5, 4, 3]), (0, [4, 3, 2, 1]), (1, [5, 4, 3, 2]), (0, [5, 4, 3, 2, 1])]

@[expose] def pkTabA6 : ℕ := 2952235702713233612810

@[expose] def pkDataA6 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 1180663682709764198402),
  (4, 4, 1180663682709831319557),
  (16, 16, 1180663683809544323073),
  (64, 64, 1180681701507393929217),
  (256, 256, 1475883663075340992513),
  (1024, 1024, 2361543533803327209473),
  (5, 5, 1180663682709848072200),
  (20, 20, 1180663684084019626005),
  (80, 80, 1180686198510757167105),
  (320, 320, 1549562566178630549505),
  (1280, 1280, 590872363470254260225),
  (21, 21, 1180663684152772542504),
  (84, 84, 1180687324958541086805),
  (336, 336, 1568018286670370914305),
  (1344, 1344, 737941996487097466881),
  (85, 85, 1180687606570956112040),
  (340, 340, 1572632224478144364885),
  (1360, 1360, 774835313132988350465),
  (341, 341, 1573785708932701897384),
  (1364, 1364, 784058685125019960661),
  (1365, 1365, 786364528134222531240)]

theorem pkTabA6_spec : ∀ a b : Fin 6, ((CartanMatrix.A 6 a b : ℤ) : ZMod 3) =
    ((GGResQTwoPacked.pkLane pkTabA6 (a.val * 6 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedA6 : GGResQTwoPacked.pkSharedOK pkTabA6 6 ([0, 1, 2, 3, 4, 5] : List (Fin 7))
    Rq2_2cce17e5c6cf7fa5 pkDataA6 = true := by
  decide +kernel

theorem pkListA6 (ib ic : Fin 6) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.A 6) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.A 6) ib ic e₁ e₂ u v k).get
      (Fin.last 7) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.A 6) ib ic e₁ e₂ u v)
        [0, 1, 2, 3, 4, 5] Rq2_2cce17e5c6cf7fa5 ∧
      ∀ r ∈ Rq2_2cce17e5c6cf7fa5, ∃ d ∈ pkDataA6, GGResQTwoPacked.pkBlkM 6
        (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.A 6) ib ic e₁ e₂ u v) r) = d.2.2 :=
  GGResQTwoPacked.pkShared_sound pkSharedA6 (GGResQTwoPacked.pkTab_std pkTabA6_spec ib ic e₁ e₂ u v)
    h2 hx

end CFSG.StandardType.GGResQTwoCellDataA6
