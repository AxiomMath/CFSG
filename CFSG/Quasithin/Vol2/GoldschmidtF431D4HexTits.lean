module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexPt
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexLn
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoAbs

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w

theorem titsModel_of_hex {α : RankTwoAmalgam.{u}} {Yb : Type w} [Group Yb]
    {ι : α.Completion Yb} (hι : ι.IsFaithful) (hP : IsGenPolygon ι.graph 6) {b₀ y₀ m₀ : ι.Γ}
    (Lp : HexPt ι.G0 ι.graph ι.xv b₀) (Ll : HexLn ι.G0 ι.graph ι.lv y₀ m₀) :
    TitsModel ι 4 := by
  have c1 : Nat.card (CosetGeom.nbrs ι.xv) = α.α1.range.index := nbrs_xv_card hι
  have c2 : Nat.card (CosetGeom.nbrs ι.lv) = α.α2.range.index := nbrs_lv_card hι
  have n1 : Nat.card (CosetGeom.nbrs ι.xv) = 9 := by
    rw [Nat.card_coe_set_eq]
    exact Lp.card
  have n2 : Nat.card (CosetGeom.nbrs ι.lv) = 3 := by
    rw [Nat.card_coe_set_eq]
    exact Ll.card
  refine ⟨hι, ?_, ?_, by norm_num, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RankTwoAmalgam.qOne
    rw [← c1, n1]
    norm_num
  · unfold RankTwoAmalgam.qTwo
    rw [← c2, n2]
  · exact fun q q' hq hq' => Lp.pathTrans hP hq hq'
  · exact fun q q' hq hq' => Ll.pathTrans5 hP hq hq'
  · exact fun p hp y hy hne => Lp.noFix hP hp hy hne
  · exact fun p hp q hq hpq y y' hy hy' => Lp.transPair hP hp hq hpq hy hy'
  · exact fun p hp q hq hpq y y' hy hy' => Ll.transPair hP hp hq hpq hy hy'

end CFSG.Quasithin.D4Hex
