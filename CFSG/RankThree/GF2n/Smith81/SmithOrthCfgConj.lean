module

public import CFSG.RankThree.GF2n.Smith81.OrthSetup
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem SmithOrthCfg.conj {M Q Z B : Subgroup G} (h : SmithOrthCfg M Q Z B) (y : G) :
    SmithOrthCfg (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) :=
  ⟨h.toCfg.conj y, h.orth.conj y⟩

end CFSG.RankThree.GF2n.Smith81
