module

public import Certificates.Certificate733010
import CFSG.Quasithin.Background.TwoM22TwoModelOfGens

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.Quasithin.G2U

open scoped commutatorElement


section Concrete


theorem rad_facts (hC : ChevFacts) : RadFacts := Certificates.certificate733010 hC

theorem Z1_eq (hC : ChevFacts) : Z1 = Subgroup.closure {pc1Y 8, pc1Y 9} := (rad_facts hC).Z1_eq

theorem card_Z1 (hC : ChevFacts) : Nat.card Z1 = 4 := (rad_facts hC).card_Z1

theorem sq_Z1 (hC : ChevFacts) : ∀ z ∈ Z1, z ^ 2 = 1 := (rad_facts hC).sq_Z1

theorem sq_Q1 (hC : ChevFacts) : ∀ x ∈ Q1, x ^ 2 ∈ Z1 := (rad_facts hC).sq_Q1

theorem comm_Q1 (hC : ChevFacts) : ∀ x ∈ Q1, ∀ y ∈ Q1, ⁅x, y⁆ ∈ Z1 := (rad_facts hC).comm_Q1

theorem Z2_eq (hC : ChevFacts) :
    Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9} :=
  (rad_facts hC).Z2_eq

theorem card_Z2 (hC : ChevFacts) : Nat.card Z2 = 16 := (rad_facts hC).card_Z2

theorem sq_Z2 (hC : ChevFacts) : ∀ z ∈ Z2, z ^ 2 = 1 := (rad_facts hC).sq_Z2

theorem sq_Q2 (hC : ChevFacts) : ∀ x ∈ Q2, x ^ 2 ∈ Z2 := (rad_facts hC).sq_Q2

theorem comm_Q2 (hC : ChevFacts) : ∀ x ∈ Q2, ∀ y ∈ Q2, ⁅x, y⁆ ∈ Z2 := (rad_facts hC).comm_Q2

theorem Q1_ne_Q2 (hC : ChevFacts) : Q1 ≠ Q2 := (rad_facts hC).Q1_ne_Q2

theorem rels_pc1Q (hC : ChevFacts) :
    ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsQ1, CFSG.Certificates.signedProd pc1Q w = 1 :=
  (rad_facts hC).rels_pc1Q

theorem rels_pc2Q (hC : ChevFacts) :
    ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsQ2, CFSG.Certificates.signedProd pc2Q w = 1 :=
  (rad_facts hC).rels_pc2Q

theorem rels_A1Q (hC : ChevFacts) :
    ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd A1Q w = 1 :=
  (rad_facts hC).rels_A1Q

theorem rels_A2Q (hC : ChevFacts) :
    ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd A2Q w = 1 :=
  (rad_facts hC).rels_A2Q

theorem rels_A1imgQ (hC : ChevFacts) :
    ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd A1imgQ w = 1 :=
  (rad_facts hC).rels_A1imgQ

theorem rels_A2imgQ (hC : ChevFacts) :
    ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd A2imgQ w = 1 :=
  (rad_facts hC).rels_A2imgQ

end Concrete

theorem M1_le_normalizer_Z1 (hN : M1 ≤ Subgroup.normalizer (Q1 : Set Y)) :
    M1 ≤ Subgroup.normalizer (Z1 : Set Y) :=
  hN.trans (CFSG.Quasithin.E3.normalizer_le_normalizer_centerOf Q1)

theorem M2_le_normalizer_Z2 (hN : M2 ≤ Subgroup.normalizer (Q2 : Set Y)) :
    M2 ≤ Subgroup.normalizer (Z2 : Set Y) :=
  hN.trans (CFSG.Quasithin.E3.normalizer_le_normalizer_centerOf Q2)

theorem closure_range_pc1Q : Subgroup.closure (Set.range pc1Q) = ⊤ :=
  CFSG.GroupTheory.closure_range_subtype_eq_top pc1Y

theorem closure_range_pc2Q : Subgroup.closure (Set.range pc2Q) = ⊤ :=
  CFSG.GroupTheory.closure_range_subtype_eq_top pc2Y

theorem closure_range_A1Q : Subgroup.closure (Set.range A1Q) = ⊤ :=
  CFSG.GroupTheory.closure_range_subtype_eq_top A1gen

theorem closure_range_A2Q : Subgroup.closure (Set.range A2Q) = ⊤ :=
  CFSG.GroupTheory.closure_range_subtype_eq_top A2gen

theorem closure_range_inv_image {A : Subgroup Y} {z : Fin 3 → ↥A}
    (hz : Subgroup.closure (Set.range z) = ⊤) :
    Subgroup.closure (Set.range ![z 0, (z 1)⁻¹, (z 2)⁻¹]) = ⊤ := by
  have h0 : z 0 ∈ Subgroup.closure (Set.range ![z 0, (z 1)⁻¹, (z 2)⁻¹]) :=
    Subgroup.subset_closure ⟨0, rfl⟩
  have h1 : z 1 ∈ Subgroup.closure (Set.range ![z 0, (z 1)⁻¹, (z 2)⁻¹]) := by
    have := Subgroup.inv_mem _ (Subgroup.subset_closure
      (show ![z 0, (z 1)⁻¹, (z 2)⁻¹] 1 ∈ Set.range ![z 0, (z 1)⁻¹, (z 2)⁻¹] from ⟨1, rfl⟩))
    simpa using this
  have h2 : z 2 ∈ Subgroup.closure (Set.range ![z 0, (z 1)⁻¹, (z 2)⁻¹]) := by
    have := Subgroup.inv_mem _ (Subgroup.subset_closure
      (show ![z 0, (z 1)⁻¹, (z 2)⁻¹] 2 ∈ Set.range ![z 0, (z 1)⁻¹, (z 2)⁻¹] from ⟨2, rfl⟩))
    simpa using this
  have hle : Subgroup.closure (Set.range z) ≤
      Subgroup.closure (Set.range ![z 0, (z 1)⁻¹, (z 2)⁻¹]) := by
    rw [Subgroup.closure_le]
    rintro x ⟨j, rfl⟩
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  exact le_antisymm le_top (hz ▸ hle)

theorem closure_range_A1imgQ : Subgroup.closure (Set.range A1imgQ) = ⊤ :=
  closure_range_inv_image closure_range_A1Q

theorem closure_range_A2imgQ : Subgroup.closure (Set.range A2imgQ) = ⊤ :=
  closure_range_inv_image closure_range_A2Q

end CFSG.Quasithin.F112R.St84.G24M
