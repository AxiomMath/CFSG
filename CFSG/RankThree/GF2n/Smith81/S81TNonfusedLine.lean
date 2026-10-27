module

public import CFSG.RankThree.GF2n.Smith81.S81TNonfused
public import CFSG.RankThree.GF2n.Smith81.S81TLineE7
public import CFSG.RankThree.GF2n.Smith81.S81TLineD6

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.MinuscT


theorem smith212ENonfusedE5_of_inputs (hFE1 : Smith24E5UniformStatement)
    (hForm : Smith24E5FormStatement) (hN : NormQuotE5Statement) (hB : ElemBoundE5Statement)
    (hCl : E5InvolClassesStatement) (hGen : StrothGenByBStatement) (h34 : Stroth34Statement) :
    Smith212ENonfusedE5Statement :=
  smith212ENonfusedE5_of_uniform hFE1 hForm hN hB hCl (fun _ _ _ _ => e7MinuscLine) hGen h34

theorem smith212ENonfusedE4_of_inputs (hFE1 : Smith24E4UniformStatement)
    (hForm : Smith24E4FormStatement) (hN : NormQuotE4Statement) (hB : ElemBoundE4Statement)
    (hCl : E4InvolClassesStatement) (hGen : StrothGenByBStatement) (h34 : Stroth34Statement) :
    Smith212ENonfusedE4Statement :=
  smith212ENonfusedE4_of_uniform hFE1 hForm hN hB hCl (fun _ _ _ _ => d6MinuscLine) hGen h34

end CFSG.RankThree.GF2n.Smith81
