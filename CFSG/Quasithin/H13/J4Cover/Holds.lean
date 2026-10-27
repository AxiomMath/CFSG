module

public import CFSG.Quasithin.H13.J4Cover.Five
public import CFSG.Quasithin.H13.J4Cover.Hat6
public import CFSG.Quasithin.H13.J4Cover.Quot
public import CFSG.Quasithin.H13.J4Cover.Transport

public section

namespace CFSG.Quasithin.H13.J4Cover


theorem j4CoverFacts_holds : CFSG.Quasithin.H13.J4CoverFacts :=
  j4CoverFacts_of_model (fun _ => le_centralizer_of_five) (fun _ => le_centralizer_of_hat6)
    exists_quotient_centralizer

end CFSG.Quasithin.H13.J4Cover
