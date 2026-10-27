module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Excl2
public import CFSG.Quasithin.EmptyFaithful.SzPS8A6
public import CFSG.Quasithin.EmptyFaithful.SzPS8A7
public import CFSG.Quasithin.EmptyFaithful.SzPS8A8
public import CFSG.Quasithin.EmptyFaithful.SzPS8G2
public import CFSG.Quasithin.EmptyFaithful.SzPS8U33
public import CFSG.Quasithin.EmptyFaithful.SzPS8M22
public import CFSG.Quasithin.EmptyFaithful.SzPS8E7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace SzPS8

theorem lemma14315ResidueS_of_inputs
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN) (hF : FieldOne1432) :
    Lemma14315ResidueS :=
  { c2 := excl2_of_parts (excl2NoNormalA5 h11 h113 h35 h37 h39 hE22 hF)
        (excl2NoNormalA6 h11 h113 h35),
    c4 := excl4_of_ovg h11 h113 h35,
    c5 := excl5_of_ovg h11 h113 h35,
    c6 := excl6_of_ovg h11 h113 h35,
    c6U33 := excl6U33S_of_ovg h11 h113 h35,
    c7 := (excl7S h11 h113 h35 h37 h39 hE22 hF),
    c11 := excl11 h11 h113 h36 h37 h39 hE22 hF,
    c13 := excl13S_of_ovg h11 h113 h35 }

theorem lemma14315SolvableS8_of_g112S
    (hG : TheoremG112FixS) (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN)
    (hF : FieldOne1432) : Lemma14315SolvableS8 :=
  lemma14315SolvableS8_of_residueS hG h11 h113 h35
    (lemma14315ResidueS_of_inputs h11 h113 h35 h36 h37 h39 hE22 hF)

end SzPS8

end CFSG.Quasithin
