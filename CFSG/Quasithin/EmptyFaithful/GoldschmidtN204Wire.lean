module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204QMain
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.Background.C1PackS15207
public import CFSG.Quasithin.EmptyFaithful.S151cA3
public import CFSG.Quasithin.EmptyFaithful.S152L01
public import CFSG.Quasithin.EmptyFaithful.S152N2Frob
public import CFSG.Quasithin.EmptyFaithful.S152O4Props

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N CFSG.Quasithin.S152N2

theorem input15204Dichotomy_of_basic
    (h113 : StageLemma14113) (h1515 : StageLemma1515CE) (h157 : StageLemma1517)
    (h1519 : StageLemma1519) (h15112 : StageLemma15112) (h15113 : StageLemma15113)
    (h15114 : StageLemma15114) (h15115 : StageTheorem15115)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hF204 : Input15204F112) :
    Input15204Dichotomy := by
  have h15201 : StageLemma15201 := stageLemma15201_of h157 h15115
  have h15202 : StageLemma15202 := stageLemma15202_of_ce h1515 h1519
  have h15203 : StageLemma15203 :=
    stageLemma15203_of_ce h113 h1515 h15113 h15114 h15201 h15202 om4IsoStatement
  have hHard : Input15205Hard :=
    C1Pack5.input15205Hard_of_ce h113 h1515 h15201 h15202 h15203 om4IsoStatement
  have h5 : StageLemma15205 := stageLemma15205_of hHard
  have h15206 : StageLemma15206 :=
    stageLemma15206_of_ce frobenius20IsSz2 h1515 h15201 h15203 h5 om4IsoStatement
  have h15207 : StageLemma15207 := stageLemma15207_of_15203 h15203
  exact input15204Dichotomy_of_F112 h37 h38 h39 h15112 h15206 h15207 hF204

end CFSG.Quasithin.He9
