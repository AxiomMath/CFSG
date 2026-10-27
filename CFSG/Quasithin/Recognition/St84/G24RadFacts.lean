module

public import CFSG.Quasithin.Recognition.St84.G24Model
public import CFSG.Certificates.WordPresentation
public import Certificates.Data.G24IdentPc

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.Quasithin.G2U

open scoped commutatorElement


structure RadFacts : Prop where
  Z1_eq : Z1 = Subgroup.closure {pc1Y 8, pc1Y 9}
  card_Z1 : Nat.card Z1 = 4
  sq_Z1 : ∀ z ∈ Z1, z ^ 2 = 1
  sq_Q1 : ∀ x ∈ Q1, x ^ 2 ∈ Z1
  comm_Q1 : ∀ x ∈ Q1, ∀ y ∈ Q1, ⁅x, y⁆ ∈ Z1
  Z2_eq : Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9}
  card_Z2 : Nat.card Z2 = 16
  sq_Z2 : ∀ z ∈ Z2, z ^ 2 = 1
  sq_Q2 : ∀ x ∈ Q2, x ^ 2 ∈ Z2
  comm_Q2 : ∀ x ∈ Q2, ∀ y ∈ Q2, ⁅x, y⁆ ∈ Z2
  Q1_ne_Q2 : Q1 ≠ Q2
  rels_pc1Q : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsQ1, CFSG.Certificates.signedProd pc1Q w = 1
  rels_pc2Q : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsQ2, CFSG.Certificates.signedProd pc2Q w = 1
  rels_A1Q : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd A1Q w = 1
  rels_A2Q : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd A2Q w = 1
  rels_A1imgQ : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA,
    CFSG.Certificates.signedProd A1imgQ w = 1
  rels_A2imgQ : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA,
    CFSG.Certificates.signedProd A2imgQ w = 1

end CFSG.Quasithin.F112R.St84.G24M
