module

public import CFSG.Quasithin.EmptyFaithful.ModHJ2
public import CFSG.Quasithin.EmptyFaithful.ModHHeEl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestJ2F
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestHeC

public section

namespace CFSG.Quasithin.ModH

theorem sylowFactsJ2_holds :
    SylowFactsJ2 :=
  sylowFactsJ2_unfolded

theorem factHeCentralizer_holds :
    FactHeCentralizer :=
  he_smallCentralizerWitness

end CFSG.Quasithin.ModH
