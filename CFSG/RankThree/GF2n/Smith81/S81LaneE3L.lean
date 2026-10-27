module

public import CFSG.RankThree.GF2n.Smith81.S81Lane28
public import CFSG.RankThree.GF2n.Smith81.S81NMain

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80


theorem smith28E3L_of_uniform (hFE1 : Smith24E3LUniformStatement) : Smith28E3LStatement :=
  fun G _ _ M Q Z B IH hc h3L X x hs =>
    e3l28Cond_of_uniform hFE1 G M Q Z B IH hc h3L X x hs
      (smith28aE3L_of_normQuot (normQuotE3L_of_uniform hFE1) (elemBoundE3L_of_uniform hFE1)
        G M Q Z B IH hc h3L X x hs)

theorem laneE3L_of_fe1 (hFE1 : Smith24E3LUniformStatement) (h34 : Stroth34Statement) :
    Smith212ENonfusedE3LStatement ∧ Smith216ECountE3LStatement ∧ Smith28E3LStatement :=
  ⟨smith212ENonfusedE3L_of_fe1 hFE1 h34,
    smith216ECountE3L_of_inputs hFE1 (eTacitE3L_of_uniform hFE1) h34,
    smith28E3L_of_uniform hFE1⟩

end CFSG.RankThree.GF2n.Smith81
