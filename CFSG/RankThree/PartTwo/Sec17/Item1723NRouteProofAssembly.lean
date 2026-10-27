module

public import CFSG.RankThree.PartTwo.Sec17.Item1723NRouteProofPara
public import CFSG.RankThree.PartTwo.Sec17.Item1723NRouteProof1727
public import CFSG.RankThree.PartTwo.Sec17.Item1724NRouteProofAssembly
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec17.Item1724NRouteProofPara

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

section Assembly


theorem configScalar_of_steps_1723N
    (h169 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item169 A (lB A) L)
    (h163 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item163 A (lB A) c L)
    (h164 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item164 A (lB A) c)
    (hM : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Claim17M A (lB A))
    (h175 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item175 A c)
    (h176 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item176 A (lB A) c L)
    (hY1 : Para1714) (hW : Para1722) (h1715 : Item1715) (h1719 : Item1719) (h1721 : Item1721)
    (h1723 : Item1723N) (h1724 : Item1724N) (h1725 : Item1725) :
    ConfigScalar :=
  configScalar_of_stepsN h169 h163 h164 hM hY1 hW (para1724_ofN h1724)
    (para1725_of_1723N Sec4.Sporadic.rank3II_4_15 h1715 h1721 h1723 h1724 h175)
    (para1726_ofN Sec4.Sporadic.rank3II_4_15 h1715 h1721 h1724 h176) h1721
    (item1724Three_of_item1724N h1724) h1725
    (item1726_ofN (item1724Three_of_item1724N h1724) h1725)
    (item1727_of_1723N Sec4.Sporadic.rank3II_4_15 h1715 h1719 h1721 h1723 h1724 h1725)

theorem item1728_of_steps_1723N
    (h169 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item169 A (lB A) L)
    (h163 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item163 A (lB A) c L)
    (h164 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item164 A (lB A) c)
    (hM : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Claim17M A (lB A))
    (h175 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item175 A c)
    (h176 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item176 A (lB A) c L)
    (hY1 : Para1714) (hW : Para1722) (h1715 : Item1715) (h1719 : Item1719) (h1721 : Item1721)
    (h1723 : Item1723N) (h1724 : Item1724N) (h1725 : Item1725) : Item1728 :=
  rank3II_17_28_of_scalar (configScalar_of_steps_1723N h169 h163 h164 hM h175 h176 hY1 hW h1715
    h1719 h1721 h1723 h1724 h1725)

theorem item1728_of_steps_named_1723N (h169 : Item169R) (h163 : Item163R) (h164 : Item164R)
    (hM : Claim17MR) (h175 : Item175R) (h176 : Item176R) (hY1 : Para1714) (hW : Para1722)
    (h1715 : Item1715) (h1719 : Item1719) (h1721 : Item1721) (h1723 : Item1723N)
    (h1724 : Item1724N) (h1725 : Item1725) : Item1728 :=
  item1728_of_steps_1723N h169 h163 h164 hM h175 h176 hY1 hW h1715 h1719 h1721 h1723 h1724 h1725

end Assembly

end CFSG.RankThree.PartTwo.Sec17
