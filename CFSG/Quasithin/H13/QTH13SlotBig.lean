module

public import CFSG.Quasithin.Background.SmithC27Holds
public import CFSG.Quasithin.Background.C48OpenKW
public import CFSG.Quasithin.Vol2.KGFactC31RuCoverFin
public import CFSG.Milestones.ASVolI.C41.BigStmt
public import CFSG.Quasithin.MS93.Burnside.C134BigProof
public import CFSG.Quasithin.MS93.Burnside.Mag568Main

public section

namespace CFSG.Quasithin.H13.SlotLeaves

theorem burnsideC134w_corrBig_holds
    : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrBig :=
  CFSG.Quasithin.MS93.burnsideC134w_corrBig CFSG.Quasithin.MS93.S4L.burnsideMag568_noNonlinSLGt4

theorem asc41Statement_forall_of_big
    (h32 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hb : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrBig) :
    ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC41Statement G :=
  fun G _ _ => CFSG.Quasithin.C41Pf.burnsideC41w_asc41Statement_of_big
    (CFSG.Quasithin.asc27Statement_of_c132 h32 G) hb

theorem asc48Statement_forall_of_big
    (h32 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hb : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrBig)
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) :
    ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC48Statement G :=
  fun G _ _ =>
    CFSG.Quasithin.C48.asc48Statement_of_kw
      (CFSG.Quasithin.C41Pf.burnsideC41w_asc41Statement_of_big
        (CFSG.Quasithin.asc27Statement_of_c132 h32 G) hb)
      (CFSG.Quasithin.asc27Statement_of_c132 h32 G) hKW
      (CFSG.Quasithin.C48Cover.c48SporCoverFact_holds (G := G))

end CFSG.Quasithin.H13.SlotLeaves
