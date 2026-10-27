module

public import Certificates.Certificate733011

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open scoped commutatorElement


theorem normal_facts (hC : ChevFacts) : NormalFacts := Certificates.certificate733011 hC

theorem eq_Q1_or_eq_Q2 (hC : ChevFacts) (hH0 : H0 ≤ B0) (hcH0 : Nat.card H0 = 9)
    (hQ1T : Q1 ≤ T0) (hQ2T : Q2 ≤ T0) (hcQ1 : Nat.card Q1 = 1024) (hcQ2 : Nat.card Q2 = 1024)
    {N : Subgroup Y} (hNB : N ≤ B0) (hBN : B0 ≤ Subgroup.normalizer (N : Set Y))
    (hN : Nat.card N = 2 ^ 10) : N = Q1 ∨ N = Q2 :=
  (normal_facts hC).eq_Q1_or_eq_Q2 hH0 hcH0 hQ1T hQ2T hcQ1 hcQ2 hNB hBN hN

theorem central_mod_Q2 (hC : ChevFacts) (hcl : Subgroup.closure (Set.range gB0) = B0)
    (hQ2T : Q2 ≤ T0) (hNQ : M2 ≤ Subgroup.normalizer (Q2 : Set Y))
    (hZ2 : Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9})
    {y : Y} (hy : y ∈ B0) (ho : orderOf y = 3) (hc : ∀ b ∈ B0, ⁅y, b⁆ ∈ Q2) :
    (∀ z ∈ Z2, y * z = z * y) ∧ Q2 ⊓ Subgroup.centralizer ({y} : Set Y) = Z2 ∧
      ∃ E : Subgroup Y, E ≤ B0 ⊓ Subgroup.centralizer ({y} : Set Y) ∧ Nat.card E = 4 ∧
        E ⊓ Z2 = ⊥ :=
  (normal_facts hC).central_mod_Q2 hcl hQ2T hNQ hZ2 hy ho hc

end CFSG.Quasithin.F112R.St84.G24M
