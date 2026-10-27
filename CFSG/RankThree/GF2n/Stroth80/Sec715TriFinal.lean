module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriMain
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriKegelB

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

theorem omega8Triality_of_smallNF (hA : SmallNFStatement) : Omega8TrialityStatement :=
  omega8Triality_of hA nfIso_holds

end CFSG.RankThree.GF2n.Stroth80.Tri
