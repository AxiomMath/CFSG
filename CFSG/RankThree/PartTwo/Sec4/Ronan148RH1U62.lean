module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1LieOrd
public import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Shape
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEU6
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Shape

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62 (P6 u6Equiv uData)

section U62


theorem noCfgS427_P6 : NoCfgS427 P6 :=
  noCfgS427_of_compShape not_isA5Type_of_excU62Type fun β h3 h1 =>
    CFSG.HardMathSupport.Dickson.Bal207.excU62_compShape_primeForm uData β h3 h1



theorem rowOf427_u62
    : RowOf427 (projSU 6 2 1) :=
  rowOf427_of_noCfgS fun S _ _ _ _ ⟨e⟩ => by
    let φ : S ≃* P6 := e.trans u6Equiv
    refine ⟨NoCfgS427.of_mulEquiv φ noCfgS427_P6, noONS427_of_card ?_⟩
    rw [Nat.card_congr φ.toEquiv]
    intro h
    have h31 : 31 ∣ 27590492160 :=
      ((show 31 ∣ 19 * 31 * 343 by norm_num).trans h).trans RonanK429E.U6.card_P6_dvd
    norm_num at h31

end U62

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
