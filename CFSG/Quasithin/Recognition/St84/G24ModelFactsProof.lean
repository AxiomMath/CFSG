module

public import CFSG.Quasithin.Recognition.St84.G24ModelFacts
import CFSG.Quasithin.Recognition.St84.G24ModelChev
import CFSG.Quasithin.Recognition.St84.G24ModelBorel
import CFSG.Quasithin.Recognition.St84.G24ModelRad
import CFSG.Quasithin.Recognition.St84.G24ModelNormal
public import CFSG.Quasithin.Recognition.St84.G24ModelChevFacts

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M


theorem facts : Facts := by
  let hC : ChevFacts := chevFacts
  exact
    { toGL_injective := hC.toGL_injective
      toGL_agY := hC.toGL_agY
      agY_invW := hC.agY_invW
      toGL_gB0 := CFSG.Quasithin.F112R.St84.G24M.toGL_gB0 hC
      gB0_mem_B0 := CFSG.Quasithin.F112R.St84.G24M.gB0_mem_B0 hC
      closure_gB0 := CFSG.Quasithin.F112R.St84.G24M.closure_gB0 hC
      T0_le_B0 := hC.T0_le_B0
      B0_le_M1 := hC.B0_le_M1
      B0_le_M2 := hC.B0_le_M2
      inf_M1_M2 := hC.inf_M1_M2
      normalizer_T0 := hC.normalizer_T0
      card_T0 := hC.card_T0
      card_B0 := hC.card_B0
      le_T0_of_isPGroup := hC.le_T0_of_isPGroup
      isSylowTwoOf_T0_M1 := hC.isSylowTwoOf_T0_M1
      isSylowTwoOf_T0_M2 := hC.isSylowTwoOf_T0_M2
      orderOf_k1Y := CFSG.Quasithin.F112R.St84.G24M.orderOf_k1Y hC
      orderOf_k2Y := CFSG.Quasithin.F112R.St84.G24M.orderOf_k2Y hC
      orderOf_xaY := CFSG.Quasithin.F112R.St84.G24M.orderOf_xaY hC
      orderOf_xbY := CFSG.Quasithin.F112R.St84.G24M.orderOf_xbY hC
      commute_k1Y_k2Y := CFSG.Quasithin.F112R.St84.G24M.commute_k1Y_k2Y hC
      commute_k1Y_xaY := CFSG.Quasithin.F112R.St84.G24M.commute_k1Y_xaY hC
      commute_k2Y_xbY := CFSG.Quasithin.F112R.St84.G24M.commute_k2Y_xbY hC
      H0_le_B0 := CFSG.Quasithin.F112R.St84.G24M.H0_le_B0 hC
      card_H0 := CFSG.Quasithin.F112R.St84.G24M.card_H0 hC
      card_Q1 := CFSG.Quasithin.F112R.St84.G24M.card_Q1 hC
      card_Q2 := CFSG.Quasithin.F112R.St84.G24M.card_Q2 hC
      card_A1 := CFSG.Quasithin.F112R.St84.G24M.card_A1 hC
      card_A2 := CFSG.Quasithin.F112R.St84.G24M.card_A2 hC
      card_Z1 := CFSG.Quasithin.F112R.St84.G24M.card_Z1 hC
      card_Z2 := CFSG.Quasithin.F112R.St84.G24M.card_Z2 hC
      Z1_eq := CFSG.Quasithin.F112R.St84.G24M.Z1_eq hC
      Z2_eq := CFSG.Quasithin.F112R.St84.G24M.Z2_eq hC
      Q1_ne_Q2 := CFSG.Quasithin.F112R.St84.G24M.Q1_ne_Q2 hC
      Q1_le_T0 := CFSG.Quasithin.F112R.St84.G24M.Q1_le_T0 hC
      Q2_le_T0 := CFSG.Quasithin.F112R.St84.G24M.Q2_le_T0 hC
      A1_le_M1 := CFSG.Quasithin.F112R.St84.G24M.A1_le_M1 hC
      A2_le_M2 := CFSG.Quasithin.F112R.St84.G24M.A2_le_M2 hC
      sup_Q1_A1 := CFSG.Quasithin.F112R.St84.G24M.sup_Q1_A1 hC
      sup_Q2_A2 := CFSG.Quasithin.F112R.St84.G24M.sup_Q2_A2 hC
      inf_A1_Q1 := CFSG.Quasithin.F112R.St84.G24M.inf_A1_Q1 hC
      inf_A2_Q2 := CFSG.Quasithin.F112R.St84.G24M.inf_A2_Q2 hC
      M1_le_normalizer_Q1 := CFSG.Quasithin.F112R.St84.G24M.M1_le_normalizer_Q1 hC
      M2_le_normalizer_Q2 := CFSG.Quasithin.F112R.St84.G24M.M2_le_normalizer_Q2 hC
      M1_le_normalizer_Z1 :=
        CFSG.Quasithin.F112R.St84.G24M.M1_le_normalizer_Z1
          (CFSG.Quasithin.F112R.St84.G24M.M1_le_normalizer_Q1 hC)
      M2_le_normalizer_Z2 :=
        CFSG.Quasithin.F112R.St84.G24M.M2_le_normalizer_Z2
          (CFSG.Quasithin.F112R.St84.G24M.M2_le_normalizer_Q2 hC)
      sq_Z1 := CFSG.Quasithin.F112R.St84.G24M.sq_Z1 hC
      sq_Z2 := CFSG.Quasithin.F112R.St84.G24M.sq_Z2 hC
      sq_Q1 := CFSG.Quasithin.F112R.St84.G24M.sq_Q1 hC
      sq_Q2 := CFSG.Quasithin.F112R.St84.G24M.sq_Q2 hC
      comm_Q1 := CFSG.Quasithin.F112R.St84.G24M.comm_Q1 hC
      comm_Q2 := CFSG.Quasithin.F112R.St84.G24M.comm_Q2 hC
      pCoreOf_M1 := CFSG.Quasithin.F112R.St84.G24M.pCoreOf_M1 hC
      pCoreOf_M2 := CFSG.Quasithin.F112R.St84.G24M.pCoreOf_M2 hC
      rels_pc1Q := CFSG.Quasithin.F112R.St84.G24M.rels_pc1Q hC
      rels_pc2Q := CFSG.Quasithin.F112R.St84.G24M.rels_pc2Q hC
      rels_A1Q := CFSG.Quasithin.F112R.St84.G24M.rels_A1Q hC
      rels_A2Q := CFSG.Quasithin.F112R.St84.G24M.rels_A2Q hC
      rels_A1imgQ := CFSG.Quasithin.F112R.St84.G24M.rels_A1imgQ hC
      rels_A2imgQ := CFSG.Quasithin.F112R.St84.G24M.rels_A2imgQ hC
      closure_range_pc1Q := CFSG.Quasithin.F112R.St84.G24M.closure_range_pc1Q
      closure_range_pc2Q := CFSG.Quasithin.F112R.St84.G24M.closure_range_pc2Q
      closure_range_A1Q := CFSG.Quasithin.F112R.St84.G24M.closure_range_A1Q
      closure_range_A2Q := CFSG.Quasithin.F112R.St84.G24M.closure_range_A2Q
      closure_range_A1imgQ := CFSG.Quasithin.F112R.St84.G24M.closure_range_A1imgQ
      closure_range_A2imgQ := CFSG.Quasithin.F112R.St84.G24M.closure_range_A2imgQ
      eq_Q1_or_eq_Q2 := fun {N} hNB hBN hN =>
        CFSG.Quasithin.F112R.St84.G24M.eq_Q1_or_eq_Q2 hC
          (CFSG.Quasithin.F112R.St84.G24M.H0_le_B0 hC)
          (CFSG.Quasithin.F112R.St84.G24M.card_H0 hC)
          (CFSG.Quasithin.F112R.St84.G24M.Q1_le_T0 hC)
          (CFSG.Quasithin.F112R.St84.G24M.Q2_le_T0 hC)
          (CFSG.Quasithin.F112R.St84.G24M.card_Q1 hC)
          (CFSG.Quasithin.F112R.St84.G24M.card_Q2 hC) hNB hBN hN
      central_mod_Q2 := fun {y} hy ho hc =>
        CFSG.Quasithin.F112R.St84.G24M.central_mod_Q2 hC
          (CFSG.Quasithin.F112R.St84.G24M.closure_gB0 hC)
          (CFSG.Quasithin.F112R.St84.G24M.Q2_le_T0 hC)
          (CFSG.Quasithin.F112R.St84.G24M.M2_le_normalizer_Q2 hC)
          (CFSG.Quasithin.F112R.St84.G24M.Z2_eq hC) hy ho hc }

end CFSG.Quasithin.F112R.St84.G24M
