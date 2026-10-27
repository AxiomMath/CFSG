module

public import CFSG.Quasithin.Background.C48SporPf
public import CFSG.Quasithin.Background.C48PfD
public import CFSG.Quasithin.Background.C48AsmLineStep
public import CFSG.Quasithin.Background.C22PfC
public import CFSG.Quasithin.Background.C22PfD
public import CFSG.Quasithin.Background.C48PfFourModPf

public section

namespace CFSG.Quasithin.C48

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem asc48Statement_of_inputs
    (hC31 : ASC31Statement G) (hC41 : ASC41Statement G)
    (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (hA3 : A3Orbits G) (hStep : ASC213Step G)
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (h27 : ASC27Statement G) (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (hInsp : InspC31Sporadic) (hCov : C48SporCoverFact G) : ASC48Statement G :=
  asc48Statement_of hC31 hC41 (C48Spor.c48SporStep_of (C22Pf.asc22One_of hA37) hInsp hCov)
    c48C41LineStep
    (C48Pf.c48C41FourStep_of (C22Pf.asc22Three_of hA37) h27 h51 hI16 hA8 C48Pf.fourModFact_holds)
    hC129 hC111 hC19 hA3 hStep h36 h38

end CFSG.Quasithin.C48
