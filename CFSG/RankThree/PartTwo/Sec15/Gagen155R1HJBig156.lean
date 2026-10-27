module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJBigON
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLe156
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

section Item156Big


theorem item156Big_of_omegaA_eq {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (hobs : Ronan153Big.Claim153ObsBig A (lB A)) (h1411 : Item1411_1 A (lB A)) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hON : Step156ON A (lB A))
    (hD : Step156D A (lB A)) (hgen : KS156HJGen) (hmeet : Step156Meet A (lB A))
    (hΩ : omegaA A = {Subgroup.zpowers c}) : Item156Big A (lB A) := by
  intro Y hY hYb
  have key := false_of_isType156_of_omegaA_eq h h148 h1411 h134 h48 h415 hON hD hgen hmeet hΩ hY
    (fun S hS => ((h153 Y hY hYb).2.1 S hS).1) (hobs Y hY hYb)
  exact ⟨⟨fun e => key (Or.inl ⟨e⟩)⟩, fun h6 => key (Or.inr (Or.inl h6)),
    fun hON' => key (Or.inr (Or.inr hON'))⟩

end Item156Big

section Item156BigR


theorem res1J2Item156Big_of (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142 : Item142AllS14) (h1411 : Item1411_1R) (h152 : Item152BigR)
    (h153 : Ronan153Big.Item153BigR) (hobs : Ronan153Big.Claim153ObsBigR) :
    Res1J2Item156Big := by
  intro G _ _ A c L hR _ hΩ
  have hS := hR.toSec14Std
  exact item156Big_of_omegaA_eq hS (h148 G A c L hR) (h153 G A c L hR) (hobs G A c L hR)
    (h1411 G A c L hR) h134 h48 h415
    (step156ON_of hS h142 (step156ONX_of h134 h48 hS (h148 G A c L hR)
      (step156ONXK_of_onk_big hS (h152 G A c L hR)
        (step156ONK_of h134 h48 hS (h148 G A c L hR)))))
    (step156D_of hS h142) (ks156HJGen_of h142) (step156Meet_of hS h142) hΩ

end Item156BigR

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
