module

public import CFSG.Quasithin.EmptyFaithful.A38c15IrrClose
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Final
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Main
public import CFSG.Quasithin.EmptyFaithful.E22NMain
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.GoldschmidtB69DeepFour
public import CFSG.Quasithin.Background.GoldschmidtC126NoN

public section

namespace CFSG.Quasithin

theorem e22StatementNoN_proved :
    E2.E22StatementNoN :=
  E2.E22N.e22StatementNoN_of_asc80
    (E2P.Asc80.asc80L3Eps_holds A38c15.sl3OddIrr A312U3.su3OddIrr_holds)

theorem theoremC126_proved :
    TheoremC126 :=
  theoremC126_holds_noN asB42_holds (B69.asB69DeepInputsFour_holds e22StatementNoN_proved)
    e22StatementNoN_proved

end CFSG.Quasithin
