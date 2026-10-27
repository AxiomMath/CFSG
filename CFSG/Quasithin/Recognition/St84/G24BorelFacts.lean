module

public import CFSG.Quasithin.Recognition.St84.G24Model
public import Certificates.Data.G24DCCode

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.Quasithin.G2U

open scoped commutatorElement


structure BorelFacts : Prop where
  toGL_gB0 : ∀ k : Fin 4, (toGL (gB0 k) : Matrix (Fin 14) (Fin 14) F4) =
    CFSG.Quasithin.St84.G24DC.Code.decode
      ((CFSG.Quasithin.St84.G24DC.Native.gBN ()).getD k.val
        CFSG.Quasithin.St84.G24DC.Native.oneM)
  gB0_mem_B0 : ∀ k : Fin 4, gB0 k ∈ B0
  closure_gB0 : Subgroup.closure (Set.range gB0) = B0
  orderOf_k1Y : orderOf k1Y = 3
  orderOf_k2Y : orderOf k2Y = 3
  orderOf_xaY : orderOf xaY = 2
  orderOf_xbY : orderOf xbY = 2
  commute_k1Y_k2Y : Commute k1Y k2Y
  commute_k1Y_xaY : Commute k1Y xaY
  commute_k2Y_xbY : Commute k2Y xbY
  H0_le_B0 : H0 ≤ B0
  card_H0 : Nat.card H0 = 9
  card_Q1 : Nat.card Q1 = 1024
  card_Q2 : Nat.card Q2 = 1024
  card_A1 : Nat.card A1 = 180
  card_A2 : Nat.card A2 = 180
  Q1_le_T0 : Q1 ≤ T0
  Q2_le_T0 : Q2 ≤ T0
  A1_le_M1 : A1 ≤ M1
  A2_le_M2 : A2 ≤ M2
  sup_Q1_A1 : Q1 ⊔ A1 = M1
  sup_Q2_A2 : Q2 ⊔ A2 = M2
  inf_A1_Q1 : A1 ⊓ Q1 = ⊥
  inf_A2_Q2 : A2 ⊓ Q2 = ⊥
  M1_le_normalizer_Q1 : M1 ≤ Subgroup.normalizer (Q1 : Set Y)
  M2_le_normalizer_Q2 : M2 ≤ Subgroup.normalizer (Q2 : Set Y)
  pCoreOf_M1 : CFSG.Open.pCoreOf 2 M1 = Q1
  pCoreOf_M2 : CFSG.Open.pCoreOf 2 M2 = Q2

structure NormalFacts : Prop where
  eq_Q1_or_eq_Q2 : H0 ≤ B0 → Nat.card H0 = 9 → Q1 ≤ T0 → Q2 ≤ T0 → Nat.card Q1 = 1024 →
    Nat.card Q2 = 1024 → ∀ {N : Subgroup Y}, N ≤ B0 → B0 ≤ Subgroup.normalizer (N : Set Y) →
      Nat.card N = 2 ^ 10 → N = Q1 ∨ N = Q2
  central_mod_Q2 : Subgroup.closure (Set.range gB0) = B0 → Q2 ≤ T0 →
    M2 ≤ Subgroup.normalizer (Q2 : Set Y) →
    Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9} →
    ∀ {y : Y}, y ∈ B0 → orderOf y = 3 → (∀ b ∈ B0, ⁅y, b⁆ ∈ Q2) →
      (∀ z ∈ Z2, y * z = z * y) ∧ Q2 ⊓ Subgroup.centralizer ({y} : Set Y) = Z2 ∧
        ∃ E : Subgroup Y, E ≤ B0 ⊓ Subgroup.centralizer ({y} : Set Y) ∧ Nat.card E = 4 ∧
          E ⊓ Z2 = ⊥

end CFSG.Quasithin.F112R.St84.G24M
