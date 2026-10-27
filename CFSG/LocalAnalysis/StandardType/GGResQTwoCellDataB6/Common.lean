module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataB6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_03f192978eefee08 : List (Fin 7 × List (Fin 7)) :=
[(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (0, [1]), (1, [2]), (2, [3]), (3, [4]), (4, [5]), (5, [4]), (0, [2, 1]), (1, [3, 2]), (2, [4, 3]), (3, [5, 4]), (5, [3, 4]), (0, [3, 2, 1]), (1, [4, 3, 2]), (2, [5, 4, 3]), (3, [4, 5, 4]), (5, [2, 3, 4]), (0, [4, 3, 2, 1]), (1, [5, 4, 3, 2]), (2, [4, 5, 4, 3]), (5, [1, 2, 3, 4]), (0, [5, 4, 3, 2, 1]), (1, [4, 5, 4, 3, 2]), (2, [3, 4, 5, 4, 3]), (5, [0, 1, 2, 3, 4]), (0, [4, 5, 4, 3, 2, 1]), (1, [3, 4, 5, 4, 3, 2]), (0, [3, 4, 5, 4, 3, 2, 1]), (1, [2, 3, 4, 5, 4, 3, 2]), (0, [2, 3, 4, 5, 4, 3, 2, 1]), (0, [1, 2, 3, 4, 5, 4, 3, 2, 1])]

@[expose] def pkTabB6 : ℕ := 2951947472337081901066

@[expose] def pkDataB6 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 1180663682709764198402),
  (4, 4, 1180663682709831319557),
  (16, 16, 1180663683809544323073),
  (64, 64, 1180681701507393929217),
  (256, 256, 1771031568254693818369),
  (1024, 1024, 2361543533803327209473),
  (5, 5, 1180663682709848072200),
  (20, 20, 1180663684084019626005),
  (80, 80, 1180686198510757167105),
  (320, 320, 1918497447652821581825),
  (2304, 1280, 2656403296567458545665),
  (1280, 1536, 1181312306609221812225),
  (21, 21, 1180663684152772542504),
  (84, 84, 1180687324958541086805),
  (336, 336, 1955399912218271498241),
  (2368, 1344, 2730568658816428163073),
  (1344, 1664, 1180663845465402392577),
  (85, 85, 1180687606570956112040),
  (340, 340, 1964625536044472336725),
  (2384, 1360, 2749019734988236865537),
  (2624, 1600, 1181348229879968055297),
  (1360, 1696, 1180663682749768024065),
  (341, 341, 1966931942003636716200),
  (2388, 1364, 2753632546861747930453),
  (2640, 1616, 1181357348143594029057),
  (1364, 1704, 1180663682709773977257),
  (2389, 1365, 2754785749841320364712),
  (2644, 1620, 1181359600177755326037),
  (2704, 1680, 1180663847636515241985),
  (1365, 1706, 1180663682709764196694),
  (2645, 1621, 1181360163196418148776),
  (2708, 1684, 1180663848214526822037),
  (2709, 1685, 1180663848351972739432),
  (2724, 1700, 1180663682749895296677),
  (2725, 1701, 1180663682749935819096),
  (2729, 1705, 1180663682709773983745)]

theorem pkTabB6_spec : ∀ a b : Fin 6, ((CartanMatrix.B 6 a b : ℤ) : ZMod 3) =
    ((GGResQTwoPacked.pkLane pkTabB6 (a.val * 6 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedB6 : GGResQTwoPacked.pkSharedOK pkTabB6 6 ([0, 1, 2, 3, 4, 5] : List (Fin 7))
    Rq2_03f192978eefee08 pkDataB6 = true := by
  decide +kernel

theorem pkListB6 (ib ic : Fin 6) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.B 6) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.B 6) ib ic e₁ e₂ u v k).get
      (Fin.last 7) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.B 6) ib ic e₁ e₂ u v)
        [0, 1, 2, 3, 4, 5] Rq2_03f192978eefee08 ∧
      ∀ r ∈ Rq2_03f192978eefee08, ∃ d ∈ pkDataB6, GGResQTwoPacked.pkBlkM 6
        (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.B 6) ib ic e₁ e₂ u v) r) = d.2.2 :=
  GGResQTwoPacked.pkShared_sound pkSharedB6 (GGResQTwoPacked.pkTab_std pkTabB6_spec ib ic e₁ e₂ u v)
    h2 hx

end CFSG.StandardType.GGResQTwoCellDataB6
