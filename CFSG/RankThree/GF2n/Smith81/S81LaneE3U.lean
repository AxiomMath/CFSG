module

public import CFSG.RankThree.GF2n.Smith81.S81UInvolMain
public import CFSG.RankThree.GF2n.Smith81.S81UNonfused
public import CFSG.RankThree.GF2n.Smith81.S81UCount
public import CFSG.RankThree.GF2n.Smith81.S81XU3

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80


theorem laneE3U_of_fe1 (hFE1 : Smith24E3UUniformStatement) (h34 : Stroth34Statement)
    (hGen : StrothGenByBStatement) :
    Smith212ENonfusedE3UStatement ∧ Smith216ECountE3UStatement ∧ Smith28E3UStatement ∧
      E3URootEltStatement := by
  have hN := normQuotE3U_of_uniform hFE1
  have h28 : Smith28E3UStatement := smith28E3U_of_FE1 hFE1
  refine ⟨smith212ENonfusedE3U_of_cond hFE1 (eTacitE3U_of_genByB hGen) h34
      (smith28aE3U_of_normQuot hN (elemBoundE3U_of_uniform hFE1))
      (e3u28Cond_of_uniform hFE1 hN u6RootTransStatement_holds u6InvariantFormStatement_holds
        u6InvolFactsStatement_holds),
    smith216ECountE3U_of_inputs hFE1 (eTacitE3U_of_genByB hGen) h34, h28,
    e3uRootElt_of_inputs hFE1 h28 h34 hGen⟩

end CFSG.RankThree.GF2n.Smith81
