module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Wire10A
public import CFSG.Quasithin.Vol2.Ch10Reselect.WAssembly701AChain

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem stmt10_0_1_of_inputsAW
    (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) (h4414 : Stmt4_4_14) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h325 : Stmt3_2_5)
    (hshape : Stmt7_0_1_shapeC) (hM22 : Stmt7_2_1_M22Hat)
    (h755 : Input7_5_5) (h612 : ASInputs.AS_E_6_12) (h443 : Stmt4_4_3Orbit')
    (kf1 : OutTwoNilpotentFact) (hspor : KG68.SporadicSylowCenterCyclic)
    (hD4 : KG68.TrialityTwoSylowCenterCyclic) (hTits : KG68.TitsSylowCenterCyclic)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC24a : ∀ (G : Type) [Group G] [Finite G], ASC24One G)
    (hMS : C134L32CorrM)
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h8213 : Stmt8_2_13_cocode) (h8214 : Stmt8_2_14) (h831 : Stmt8_3_1)
    (h316 : Theorem316Statement) (h9A : Stmt9_omegaPlusA) (h4213 : Stmt4_2_13FF) : Stmt10_0_1 :=
  have h63 : ASInputs.AS_E_6_3 := CFSG.Quasithin.E6.as_E_6_3_of_thm104_insp
    CFSG.Quasithin.Asc81c.Pf.thm104 CFSG.Quasithin.E6.e623A6Insp_holds
  stmt10_0_1_of_remainingA
    ⟨CFSG.Quasithin.H13.Ch9.stmt7_0_1A_of_rowsW hE22 h331 h4414 hC58 h317 h325 hshape hM22 h755
      h612 h443 kf1 hspor hD4 hTits hC27 hC24a hMS hC48 h8213 h8214 h831 h316 h9A, h331, h4213,
      h443, h63⟩

end CFSG.Quasithin.Vol2.Ch10
