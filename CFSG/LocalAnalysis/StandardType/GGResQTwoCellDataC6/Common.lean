module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataC6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_03f192978eefee08 : List (Fin 7 × List (Fin 7)) :=
[(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (0, [1]), (1, [2]), (2, [3]), (3, [4]), (4, [5]), (5, [4]), (0, [2, 1]), (1, [3, 2]), (2, [4, 3]), (3, [5, 4]), (5, [3, 4]), (0, [3, 2, 1]), (1, [4, 3, 2]), (2, [5, 4, 3]), (3, [4, 5, 4]), (5, [2, 3, 4]), (0, [4, 3, 2, 1]), (1, [5, 4, 3, 2]), (2, [4, 5, 4, 3]), (5, [1, 2, 3, 4]), (0, [5, 4, 3, 2, 1]), (1, [4, 5, 4, 3, 2]), (2, [3, 4, 5, 4, 3]), (5, [0, 1, 2, 3, 4]), (0, [4, 5, 4, 3, 2, 1]), (1, [3, 4, 5, 4, 3, 2]), (0, [3, 4, 5, 4, 3, 2, 1]), (1, [2, 3, 4, 5, 4, 3, 2]), (0, [2, 3, 4, 5, 4, 3, 2, 1]), (0, [1, 2, 3, 4, 5, 4, 3, 2, 1])]

@[expose] def pkTabC6 : ℕ := 2657087797533880786954

@[expose] def pkDataC6 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 1180663682709764198402),
  (4, 4, 1180663682709831319557),
  (16, 16, 1180663683809544323073),
  (64, 64, 1180681701507393929217),
  (256, 256, 1475883663075340992513),
  (1024, 1024, 2361831764179478921217),
  (5, 5, 1180663682709848072200),
  (20, 20, 1180663684084019626005),
  (80, 80, 1180686198510757167105),
  (320, 320, 1549562566178630549505),
  (1280, 2304, 2951551272115555549185),
  (1536, 1280, 1181024146601814278145),
  (21, 21, 1180663684152772542504),
  (84, 84, 1180687324958541086805),
  (336, 336, 1568018286670370914305),
  (1344, 2368, 3099791700315206598657),
  (1664, 1344, 1180663775113838084097),
  (85, 85, 1180687606570956112040),
  (340, 340, 1572632224478144364885),
  (1360, 2384, 3136689590895113486337),
  (1600, 2624, 1181059999520996212737),
  (1696, 1360, 1180663682732592349185),
  (341, 341, 1573785708932701897384),
  (1364, 2388, 3145914088804223420757),
  (1616, 2640, 1181069188119010820097),
  (1704, 1364, 1180663682709769783977),
  (1365, 2389, 3148220213288406894248),
  (1620, 2644, 1181071440170343598677),
  (1680, 2704, 1180663777267775258625),
  (1706, 1365, 1180663682709764195670),
  (1621, 2645, 1181072003189010613672),
  (1684, 2708, 1180663777862958320277),
  (1685, 2709, 1180663778000408429928),
  (1700, 2724, 1180663682732715428517),
  (1701, 2725, 1180663682732760143192),
  (1705, 2729, 1180663682709769789441)]

theorem pkTabC6_spec : ∀ a b : Fin 6, ((CartanMatrix.C 6 a b : ℤ) : ZMod 3) =
    ((GGResQTwoPacked.pkLane pkTabC6 (a.val * 6 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedC6 : GGResQTwoPacked.pkSharedOK pkTabC6 6 ([0, 1, 2, 3, 4, 5] : List (Fin 7))
    Rq2_03f192978eefee08 pkDataC6 = true := by
  decide +kernel

theorem pkListC6 (ib ic : Fin 6) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.C 6) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.C 6) ib ic e₁ e₂ u v k).get
      (Fin.last 7) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.C 6) ib ic e₁ e₂ u v)
        [0, 1, 2, 3, 4, 5] Rq2_03f192978eefee08 ∧
      ∀ r ∈ Rq2_03f192978eefee08, ∃ d ∈ pkDataC6, GGResQTwoPacked.pkBlkM 6
        (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.C 6) ib ic e₁ e₂ u v) r) = d.2.2 :=
  GGResQTwoPacked.pkShared_sound pkSharedC6 (GGResQTwoPacked.pkTab_std pkTabC6_spec ib ic e₁ e₂ u v)
    h2 hx

end CFSG.StandardType.GGResQTwoCellDataC6
