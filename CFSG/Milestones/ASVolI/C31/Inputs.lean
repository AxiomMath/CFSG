module

public import CFSG.Milestones.ASVolI.C3LieType
public import CFSG.Quasithin.Vol2.KGFactC31SporHolds

public section

namespace CFSG.ASVolI

theorem burnsideC31_outSolvable
    (G : Type) [Group G] [Finite G] :
    ∀ K : Subgroup G, CFSG.Quasithin.IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      CFSG.Quasithin.OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
  fun K hK hq => CFSG.Quasithin.C41Pf.outSolvable_of_isSQTKIn K hK hq

theorem burnsideC31_inspC33 :
    CFSG.Quasithin.InspC33 :=
  CFSG.Quasithin.H13.InspC33P.inspC33_holds

section LieStep

theorem burnsideC31_c31LieStep
    (G : Type) [Group G] [Finite G] :
    CFSG.Quasithin.C31LieStep G := by
  have hA37 := CFSG.Quasithin.H13.a3ForSQTK_holds.1
  have hA38 := CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
  have hA3 : CFSG.Quasithin.A3Orbits G := CFSG.Quasithin.a3Orbits_of_a37_a38 hA37 hA38
  have hSch : ∀ K : Subgroup G, CFSG.Quasithin.IsSQTKIn K →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      CFSG.Quasithin.OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
    fun K hK hq => CFSG.Quasithin.C41Pf.outSolvable_of_isSQTKIn K hK hq
  have h22 : CFSG.Quasithin.ASC22Statement G := CFSG.Quasithin.C22Pf.asc22Statement_holds hA37
  exact burnsideC3h_c31LieStep_of CFSG.Quasithin.C35Pf.inspC35_holds
    (burnsideC2h_c27_of_noSp4Quot G) h22.1 h22.2.1 h22.2.2.2 hA3
    (CFSG.Quasithin.H13.VolI.asc129Statement_holds G) (CFSG.Quasithin.asc111Statement_holds G)
    (CFSG.Quasithin.asc19Statement_holds G) CFSG.Quasithin.H13.VolI.a36ForSQTK_holds hA38 hSch
    CFSG.Quasithin.H13.InspC33P.inspC33_holds CFSG.Quasithin.schurMult2Sp4_holds
    CFSG.Quasithin.schurMult2L42_holds CFSG.Quasithin.schurMult2L52_holds

end LieStep

theorem burnsideC31_inspC31Sporadic_of_KW
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) : CFSG.Quasithin.InspC31Sporadic :=
  CFSG.Quasithin.KGC31.inspC31Sporadic_holds' hKW

end CFSG.ASVolI
