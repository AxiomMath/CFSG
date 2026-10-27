module

public import CFSG.RankThree.GF2n.Smith81.S81Lane28
public import CFSG.RankThree.GF2n.Smith81.S81UCond
public import CFSG.RankThree.GF2n.Smith81.S81UNormQuot

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem smith28E3U_of_cond (hA : Smith28aE3UStatement) (hC : E3U28CondStatement) :
    Smith28E3UStatement := fun G _ _ M Q Z B IH hc h3U X x hs =>
  hC G M Q Z B IH hc h3U X x hs (hA G M Q Z B IH hc h3U X x hs)

theorem smith28E3U_of_uniform
    (hFE1 : Smith24E3UUniformStatement) (hInv : U6InvolFactsStatement) : Smith28E3UStatement :=
  smith28E3U_of_cond
    (smith28aE3U_of_normQuot (normQuotE3U_of_uniform hFE1) (elemBoundE3U_of_uniform hFE1))
    (e3u28Cond_of_uniform hFE1 (normQuotE3U_of_uniform hFE1) u6RootTransStatement_holds
      u6InvariantFormStatement_holds hInv)

end CFSG.RankThree.GF2n.Smith81
