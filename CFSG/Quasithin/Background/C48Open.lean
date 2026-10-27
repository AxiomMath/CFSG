module

public import CFSG.Quasithin.Background.C48Inputs
public import CFSG.Quasithin.Background.C31Open
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Background.F918F3
public import CFSG.Quasithin.Background.C35InspAll
public import CFSG.Quasithin.Background.C213NonQHolds

public section

namespace CFSG.Quasithin.C48

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem asc48Statement_of_open
    (hC41 : ASC41Statement G) (hStep : ASC213Step G) (h27 : ASC27Statement G)
    (hInsp : InspC31Sporadic) (hInsp35 : InspC35) (hCov : C48SporCoverFact G) :
    ASC48Statement G :=
  have hA37 := H13.a3ForSQTK_holds.1
  have hA38 := H13.a3ForSQTK_holds.2.1
  asc48Statement_of_inputs (C31.asc31Statement_of_open hC41 hInsp hInsp35) hC41
    (H13.VolI.asc129Statement_holds G) (asc111Statement_holds G) (asc19Statement_holds G)
    (a3Orbits_of_a37_a38 hA37 hA38) hStep H13.VolI.a36ForSQTK_holds hA37 hA38 h27 B5.asB51_holds
    asI16Cover_of asI16CoverA8_of hInsp hCov

theorem asc48Statement_of_open'
    (hC41 : ASC41Statement G) (hStep : ASC213Step G) (h27 : ASC27Statement G)
    (hInsp : InspC31Sporadic) (hCov : C48SporCoverFact G) : ASC48Statement G :=
  asc48Statement_of_open hC41 hStep h27 hInsp C35Pf.inspC35_holds hCov

theorem asc48Statement_of_open''
    (hC41 : ASC41Statement G) (h27 : ASC27Statement G) (hInsp : InspC31Sporadic)
    (hCov : C48SporCoverFact G) : ASC48Statement G :=
  asc48Statement_of_open' hC41 (C213NonQ.asc213Step_holds G) h27 hInsp hCov

end CFSG.Quasithin.C48
