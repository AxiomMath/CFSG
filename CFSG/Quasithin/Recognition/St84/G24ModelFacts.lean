module

public import CFSG.Quasithin.Recognition.St84.G24Model
public import Certificates.Data.G24IdentWit
public import CFSG.Certificates.WordPresentation

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.Quasithin.G2U

open scoped commutatorElement


structure Facts : Prop where
  toGL_injective : Function.Injective toGL
  toGL_agY : ∀ w : List (Fin 6 × Bool), (toGL (agY w) : Matrix (Fin 14) (Fin 14) F4) =
    CFSG.LieType.Multipliers.G24.toMat 14 (CFSG.LieType.Multipliers.G24.wordArr w)
  agY_invW : ∀ w : List (Fin 6 × Bool), agY (CFSG.Quasithin.St84.G24Wit.invW w) = (agY w)⁻¹
  toGL_gB0 : ∀ k : Fin 4, (toGL (gB0 k) : Matrix (Fin 14) (Fin 14) F4) =
    CFSG.Quasithin.St84.G24DC.Code.decode
      ((CFSG.Quasithin.St84.G24DC.Native.gBN ()).getD k.val
        CFSG.Quasithin.St84.G24DC.Native.oneM)
  gB0_mem_B0 : ∀ k : Fin 4, gB0 k ∈ B0
  closure_gB0 : Subgroup.closure (Set.range gB0) = B0
  T0_le_B0 : T0 ≤ B0
  B0_le_M1 : B0 ≤ M1
  B0_le_M2 : B0 ≤ M2
  inf_M1_M2 : M1 ⊓ M2 = B0
  normalizer_T0 : Subgroup.normalizer (T0 : Set Y) = B0
  card_T0 : Nat.card T0 = 4096
  card_B0 : Nat.card B0 = 36864
  le_T0_of_isPGroup : ∀ {N : Subgroup Y}, N ≤ B0 → IsPGroup 2 N → N ≤ T0
  isSylowTwoOf_T0_M1 : CFSG.QuasithinUnique.IsSylowTwoOf T0 M1
  isSylowTwoOf_T0_M2 : CFSG.QuasithinUnique.IsSylowTwoOf T0 M2
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
  card_Z1 : Nat.card Z1 = 4
  card_Z2 : Nat.card Z2 = 16
  Z1_eq : Z1 = Subgroup.closure {pc1Y 8, pc1Y 9}
  Z2_eq : Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9}
  Q1_ne_Q2 : Q1 ≠ Q2
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
  M1_le_normalizer_Z1 : M1 ≤ Subgroup.normalizer (Z1 : Set Y)
  M2_le_normalizer_Z2 : M2 ≤ Subgroup.normalizer (Z2 : Set Y)
  sq_Z1 : ∀ z ∈ Z1, z ^ 2 = 1
  sq_Z2 : ∀ z ∈ Z2, z ^ 2 = 1
  sq_Q1 : ∀ x ∈ Q1, x ^ 2 ∈ Z1
  sq_Q2 : ∀ x ∈ Q2, x ^ 2 ∈ Z2
  comm_Q1 : ∀ x ∈ Q1, ∀ y ∈ Q1, ⁅x, y⁆ ∈ Z1
  comm_Q2 : ∀ x ∈ Q2, ∀ y ∈ Q2, ⁅x, y⁆ ∈ Z2
  pCoreOf_M1 : CFSG.Open.pCoreOf 2 M1 = Q1
  pCoreOf_M2 : CFSG.Open.pCoreOf 2 M2 = Q2
  rels_pc1Q : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsQ1, CFSG.Certificates.signedProd pc1Q w = 1
  rels_pc2Q : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsQ2, CFSG.Certificates.signedProd pc2Q w = 1
  rels_A1Q : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd A1Q w = 1
  rels_A2Q : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd A2Q w = 1
  rels_A1imgQ : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA,
    CFSG.Certificates.signedProd A1imgQ w = 1
  rels_A2imgQ : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA,
    CFSG.Certificates.signedProd A2imgQ w = 1
  closure_range_pc1Q : Subgroup.closure (Set.range pc1Q) = ⊤
  closure_range_pc2Q : Subgroup.closure (Set.range pc2Q) = ⊤
  closure_range_A1Q : Subgroup.closure (Set.range A1Q) = ⊤
  closure_range_A2Q : Subgroup.closure (Set.range A2Q) = ⊤
  closure_range_A1imgQ : Subgroup.closure (Set.range A1imgQ) = ⊤
  closure_range_A2imgQ : Subgroup.closure (Set.range A2imgQ) = ⊤
  eq_Q1_or_eq_Q2 : ∀ {N : Subgroup Y}, N ≤ B0 → B0 ≤ Subgroup.normalizer (N : Set Y) →
    Nat.card N = 2 ^ 10 → N = Q1 ∨ N = Q2
  central_mod_Q2 : ∀ {y : Y}, y ∈ B0 → orderOf y = 3 → (∀ b ∈ B0, ⁅y, b⁆ ∈ Q2) →
    (∀ z ∈ Z2, y * z = z * y) ∧ Q2 ⊓ Subgroup.centralizer ({y} : Set Y) = Z2 ∧
      ∃ E : Subgroup Y, E ≤ B0 ⊓ Subgroup.centralizer ({y} : Set Y) ∧ Nat.card E = 4 ∧
        E ⊓ Z2 = ⊥

structure Witnesses where
  W1 : Fin 4 → MulAut ↥M1
  W2 : Fin 8 → MulAut ↥M2
  W1_mem : ∀ (i : Fin 4) (x : ↥M1), (x : Y) ∈ M2 ↔ ((W1 i x : ↥M1) : Y) ∈ M2
  W2_mem : ∀ (j : Fin 8) (x : ↥M2), (x : Y) ∈ M1 ↔ ((W2 j x : ↥M2) : Y) ∈ M1
  W1_gB0 : ∀ (i : Fin 4) (k : Fin 4) (x : ↥M1), (x : Y) = gB0 k →
    ((W1 i x : ↥M1) : Y) =
      (((CFSG.Quasithin.St84.G24DC.wWords.getD i.val []).getD k.val []).map gB0).prod
  W2_gB0 : ∀ (j : Fin 8) (k : Fin 4) (x : ↥M2), (x : Y) = gB0 k →
    ((W2 j x : ↥M2) : Y) =
      (((CFSG.Quasithin.St84.G24DC.wWords.getD (4 + j.val) []).getD k.val []).map gB0).prod

end CFSG.Quasithin.F112R.St84.G24M
