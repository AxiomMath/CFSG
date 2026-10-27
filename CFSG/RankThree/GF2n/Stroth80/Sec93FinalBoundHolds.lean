module

public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalBoundPure
public import CFSG.RankThree.GF2n.Stroth80.Sec93OutAssembly
public import CFSG.RankThree.GF2n.Stroth80.Sec93CentAssembly
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseA2
public import CFSG.RankThree.GF2n.Smith81.OrthE1KF7

public section

namespace CFSG.RankThree.GF2n.Stroth80


theorem listWCBound_holds : ListWCBoundStatement :=
  listWCBound_of_listFacts listCentralizerInvolutions_holds listOutElemAbelianBound_holds
    (fun _ _ _ h => Smith81.Smith23E1.listGroup_isSimpleGroup h)
    (fun _ _ _ h => Smith81.Smith23E1.kf7_listGroup_exists_noncomm h)

end CFSG.RankThree.GF2n.Stroth80
