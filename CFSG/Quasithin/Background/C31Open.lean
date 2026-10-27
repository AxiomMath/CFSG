module

public import CFSG.Quasithin.Background.C31AsmPf
public import CFSG.Quasithin.Background.C35Pf
public import CFSG.Quasithin.Background.C22PfI
public import CFSG.Quasithin.Background.C41PfK
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.Background.GoldschmidtTDC19
public import CFSG.Quasithin.H13.L32NA3SQTK
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.H13.InspC33Holds

public section

namespace CFSG.Quasithin.C31

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem asc31Statement_of_open
    (hC41 : ASC41Statement G) (hInsp : InspC31Sporadic) (hInsp35 : InspC35) :
    ASC31Statement G :=
  have hA37 := H13.a3ForSQTK_holds.1
  have hA38 := H13.a3ForSQTK_holds.2.1
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 hA37 hA38
  have hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) := fun K hK hq => C41Pf.outSolvable_of_isSQTKIn K hK hq
  have h22 : ASC22Statement G := C22Pf.asc22Statement_holds hA37
  have hInsp33 : InspC33 := H13.InspC33P.inspC33_holds
  asc31Statement_of_inputs H13.VolI.a36ForSQTK_holds hA37 hA38 hA3 hSch hInsp33 hInsp
    (C35.c31LieStep_of hInsp35 hC41 h22.1 h22.2.1 h22.2.2.2 hA3 (H13.VolI.asc129Statement_holds G)
      (asc111Statement_holds G) (asc19Statement_holds G) H13.VolI.a36ForSQTK_holds hA38 hSch
      hInsp33 schurMult2Sp4_holds schurMult2L42_holds schurMult2L52_holds)

end CFSG.Quasithin.C31
