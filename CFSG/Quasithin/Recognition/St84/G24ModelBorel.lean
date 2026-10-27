module

public import Certificates.Certificate733008

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.Quasithin.G2U


theorem borel_facts (hC : ChevFacts) : BorelFacts := Certificates.certificate733008 hC

theorem toGL_gB0 (hC : ChevFacts) (k : Fin 4) :
    (toGL (gB0 k) : Matrix (Fin 14) (Fin 14) F4) =
      CFSG.Quasithin.St84.G24DC.Code.decode
        ((CFSG.Quasithin.St84.G24DC.Native.gBN ()).getD k.val
          CFSG.Quasithin.St84.G24DC.Native.oneM) :=
  (borel_facts hC).toGL_gB0 k

theorem gB0_mem_B0 (hC : ChevFacts) (k : Fin 4) : gB0 k ∈ B0 := (borel_facts hC).gB0_mem_B0 k

theorem closure_gB0 (hC : ChevFacts) : Subgroup.closure (Set.range gB0) = B0 :=
  (borel_facts hC).closure_gB0

theorem orderOf_k1Y (hC : ChevFacts) : orderOf k1Y = 3 := (borel_facts hC).orderOf_k1Y

theorem orderOf_k2Y (hC : ChevFacts) : orderOf k2Y = 3 := (borel_facts hC).orderOf_k2Y

theorem orderOf_xaY (hC : ChevFacts) : orderOf xaY = 2 := (borel_facts hC).orderOf_xaY

theorem orderOf_xbY (hC : ChevFacts) : orderOf xbY = 2 := (borel_facts hC).orderOf_xbY

theorem commute_k1Y_k2Y (hC : ChevFacts) : Commute k1Y k2Y := (borel_facts hC).commute_k1Y_k2Y

theorem commute_k1Y_xaY (hC : ChevFacts) : Commute k1Y xaY := (borel_facts hC).commute_k1Y_xaY

theorem commute_k2Y_xbY (hC : ChevFacts) : Commute k2Y xbY := (borel_facts hC).commute_k2Y_xbY

theorem H0_le_B0 (hC : ChevFacts) : H0 ≤ B0 := (borel_facts hC).H0_le_B0

theorem card_H0 (hC : ChevFacts) : Nat.card H0 = 9 := (borel_facts hC).card_H0

theorem card_Q1 (hC : ChevFacts) : Nat.card Q1 = 1024 := (borel_facts hC).card_Q1

theorem card_Q2 (hC : ChevFacts) : Nat.card Q2 = 1024 := (borel_facts hC).card_Q2

theorem Q1_le_T0 (hC : ChevFacts) : Q1 ≤ T0 := (borel_facts hC).Q1_le_T0

theorem Q2_le_T0 (hC : ChevFacts) : Q2 ≤ T0 := (borel_facts hC).Q2_le_T0

theorem card_A1 (hC : ChevFacts) : Nat.card A1 = 180 := (borel_facts hC).card_A1

theorem card_A2 (hC : ChevFacts) : Nat.card A2 = 180 := (borel_facts hC).card_A2

theorem A1_le_M1 (hC : ChevFacts) : A1 ≤ M1 := (borel_facts hC).A1_le_M1

theorem A2_le_M2 (hC : ChevFacts) : A2 ≤ M2 := (borel_facts hC).A2_le_M2

theorem sup_Q1_A1 (hC : ChevFacts) : Q1 ⊔ A1 = M1 := (borel_facts hC).sup_Q1_A1

theorem sup_Q2_A2 (hC : ChevFacts) : Q2 ⊔ A2 = M2 := (borel_facts hC).sup_Q2_A2

theorem inf_A1_Q1 (hC : ChevFacts) : A1 ⊓ Q1 = ⊥ := (borel_facts hC).inf_A1_Q1

theorem inf_A2_Q2 (hC : ChevFacts) : A2 ⊓ Q2 = ⊥ := (borel_facts hC).inf_A2_Q2

theorem M1_le_normalizer_Q1 (hC : ChevFacts) : M1 ≤ Subgroup.normalizer (Q1 : Set Y) :=
  (borel_facts hC).M1_le_normalizer_Q1

theorem M2_le_normalizer_Q2 (hC : ChevFacts) : M2 ≤ Subgroup.normalizer (Q2 : Set Y) :=
  (borel_facts hC).M2_le_normalizer_Q2

theorem pCoreOf_M1 (hC : ChevFacts) : CFSG.Open.pCoreOf 2 M1 = Q1 := (borel_facts hC).pCoreOf_M1

theorem pCoreOf_M2 (hC : ChevFacts) : CFSG.Open.pCoreOf 2 M2 = Q2 := (borel_facts hC).pCoreOf_M2

end CFSG.Quasithin.F112R.St84.G24M
