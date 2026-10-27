module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataD6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_083533c7c9cbee7d : List (Fin 7 × List (Fin 7)) :=
[(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (0, [1]), (1, [2]), (2, [3]), (3, [4]), (3, [5]), (0, [2, 1]), (1, [3, 2]), (2, [4, 3]), (2, [5, 3]), (3, [5, 4]), (0, [3, 2, 1]), (1, [4, 3, 2]), (1, [5, 3, 2]), (2, [5, 4, 3]), (0, [4, 3, 2, 1]), (0, [5, 3, 2, 1]), (1, [5, 4, 3, 2]), (2, [3, 5, 4, 3]), (0, [5, 4, 3, 2, 1]), (1, [3, 5, 4, 3, 2]), (0, [3, 5, 4, 3, 2, 1]), (1, [2, 3, 5, 4, 3, 2]), (0, [2, 3, 5, 4, 3, 2, 1]), (0, [1, 2, 3, 5, 4, 3, 2, 1])]

open GGResQTwoPacked

@[expose] def pkTabD6 : ℕ := 2508937524929389305866

@[expose] def pkDataD6 : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 1180663682709764198402),
  (4, 4, 1180663682709831319557),
  (16, 16, 1180663683809544323073),
  (64, 64, 1254468677802232135681),
  (256, 256, 1180735757895988166657),
  (1024, 1024, 2361255373795919675393),
  (5, 5, 1180663682709848072200),
  (20, 20, 1180663684084019626005),
  (80, 80, 1272919918879304925185),
  (320, 320, 1549562566178630549505),
  (1088, 1088, 147952395714385952769),
  (21, 21, 1180663684152772542504),
  (84, 84, 1277532731345516232789),
  (336, 336, 1568018286670370914305),
  (1104, 1104, 184850251139980279809),
  (1344, 1344, 738482256918567993345),
  (85, 85, 1278685934462538105000),
  (340, 340, 1572632224478144364885),
  (1108, 1108, 194074749040507618389),
  (1360, 1360, 775384845746015911937),
  (341, 341, 1573785708932701897384),
  (1109, 1109, 196380873524688996520),
  (1364, 1364, 784610469812739114325),
  (1424, 1424, 1180663865228700237825),
  (1365, 1365, 786916875840614582952),
  (1428, 1428, 1180663865802418947477),
  (1429, 1429, 1180663865939863816808),
  (1444, 1444, 1180663682754190263717),
  (1445, 1445, 1180663682754229738072),
  (1449, 1449, 1180663682709775032321)]

theorem pkTabD6_spec : ∀ a b : Fin 6, ((CartanMatrix.D 6 a b : ℤ) : ZMod 3) =
    ((pkLane pkTabD6 (a.val * 6 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedD6 :
    pkSharedOK pkTabD6 6 ([0, 1, 2, 3, 4, 5] : List (Fin 7)) Rq2_083533c7c9cbee7d pkDataD6 =
      true := by
  decide +kernel

theorem pkListD6 (ib ic : Fin 6) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.D 6) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k,
      (ggStdTableI (Int.cast) (CartanMatrix.D 6) ib ic e₁ e₂ u v k).get (Fin.last 7) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.D 6) ib ic e₁ e₂ u v)
        [0, 1, 2, 3, 4, 5] Rq2_083533c7c9cbee7d ∧
      ∀ r ∈ Rq2_083533c7c9cbee7d, ∃ d ∈ pkDataD6,
        pkBlkM 6 (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.D 6) ib ic e₁ e₂ u v) r) =
          d.2.2 :=
  pkShared_sound pkSharedD6 (pkTab_std pkTabD6_spec ib ic e₁ e₂ u v) h2 hx

end CFSG.StandardType.GGResQTwoCellDataD6
