module

public import CFSG.Quasithin.EmptyFaithful.T1531Final2
public import CFSG.Quasithin.EmptyFaithful.T1531In47
public import CFSG.Quasithin.EmptyFaithful.T1531In62
public import CFSG.Quasithin.EmptyFaithful.T1531In63
public import CFSG.Quasithin.EmptyFaithful.T1531In66b
public import CFSG.Quasithin.EmptyFaithful.T1531In68b
public import CFSG.Quasithin.Background.C1PackS15349
public import CFSG.Quasithin.Background.C1PackS15367

public section

namespace CFSG.Quasithin

theorem stageTheorem1531_of_inputsD (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hF : F6.TheoremF618) (i44 : Stage15344) (i46 : Stage15346Four) (i49 : Stage15349Core)
    (i50 : Stage15350) (i65 : Stage15365One) (i67 : Stage15367B) (i68 : Stage15368Rest2)
    (iI : Stage1531InspectB) : StageTheorem1531 :=
  stageTheorem1531_of_inputsB h113 hF i44 (stage15346_of_four i46) stage15347 (stage15348 h11 h113)
      (stage15349_of_core h11 h113 i49) i50 (stage15362 h11) stage15363 i65 (stage15366B h11 h113)
      i67 (stage15368B_of_rest2 h113 i68) iI

theorem stageTheorem1531_of_inputsE (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hF : F6.TheoremF618) (i44 : Stage15344) (i46 : Stage15346Four) (i49 : Stage15349Core)
    (i50 : Stage15350) (i65 : Stage15365One) (i67 : Stage15367Rest) (i68 : Stage15368Rest2)
    (iI : Stage1531InspectB) : StageTheorem1531 :=
  stageTheorem1531_of_inputsD h11 h113 hF i44 i46 i49 i50 i65 (stage15367B_of_rest h113 i67) i68 iI

end CFSG.Quasithin
