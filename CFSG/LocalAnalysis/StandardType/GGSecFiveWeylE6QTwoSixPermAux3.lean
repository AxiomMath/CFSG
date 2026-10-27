module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux2
public import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement
open scoped Pointwise

variable {K : Type} [Field K] [Finite K]

theorem card_inf_sup_mul_card_inf
    {G : Type} [Group G] [Finite G] {L B C : Subgroup G}
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hCL : C ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(C ⊓ (L ⊔ B)) * Nat.card ↥(B ⊓ L) =
      Nat.card ↥(C ⊓ L) * Nat.card ↥(B ⊓ (L ⊔ C)) := by
  classical
  let Q : Subgroup G := (L ⊔ B) ⊓ (L ⊔ C)
  have hQnorm : Q ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans (sup_le Subgroup.le_normalizer hBL)
  have hmod1 : (C ⊓ (L ⊔ B)) ⊔ L = Q := by
    have h := Subgroup.inf_sup_assoc_of_le (H := C) (K := L ⊔ B) (N := L) hCL le_sup_left
    rw [inf_comm (L ⊔ B) C, sup_comm C L] at h
    exact h
  have hmod2 : (B ⊓ (L ⊔ C)) ⊔ L = Q := by
    have h := Subgroup.inf_sup_assoc_of_le (H := B) (K := L ⊔ C) (N := L) hBL le_sup_left
    rw [inf_comm (L ⊔ C) B, sup_comm B L] at h
    exact h.trans (inf_comm (L ⊔ C) (L ⊔ B))
  have hinf1 : (C ⊓ (L ⊔ B)) ⊓ L = C ⊓ L := by
    rw [inf_assoc]
    congr 1
    exact inf_eq_right.mpr le_sup_left
  have hinf2 : (B ⊓ (L ⊔ C)) ⊓ L = B ⊓ L := by
    rw [inf_assoc]
    congr 1
    exact inf_eq_right.mpr le_sup_left
  have h1 : Nat.card ↥Q * Nat.card ↥(C ⊓ L) =
      Nat.card ↥(C ⊓ (L ⊔ B)) * Nat.card ↥L := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := C ⊓ (L ⊔ B)) (K := L) (inf_le_left.trans hCL)
    rwa [hmod1, hinf1] at h
  have h2 : Nat.card ↥Q * Nat.card ↥(B ⊓ L) =
      Nat.card ↥(B ⊓ (L ⊔ C)) * Nat.card ↥L := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := B ⊓ (L ⊔ C)) (K := L) (inf_le_left.trans hBL)
    rwa [hmod2, hinf2] at h
  have hmain : Nat.card ↥(C ⊓ (L ⊔ B)) * Nat.card ↥(B ⊓ L) * Nat.card ↥L =
      Nat.card ↥(C ⊓ L) * Nat.card ↥(B ⊓ (L ⊔ C)) * Nat.card ↥L := by
    calc Nat.card ↥(C ⊓ (L ⊔ B)) * Nat.card ↥(B ⊓ L) * Nat.card ↥L
        = (Nat.card ↥(C ⊓ (L ⊔ B)) * Nat.card ↥L) * Nat.card ↥(B ⊓ L) := by ring
      _ = (Nat.card ↥Q * Nat.card ↥(C ⊓ L)) * Nat.card ↥(B ⊓ L) := by rw [← h1]
      _ = (Nat.card ↥Q * Nat.card ↥(B ⊓ L)) * Nat.card ↥(C ⊓ L) := by ring
      _ = (Nat.card ↥(B ⊓ (L ⊔ C)) * Nat.card ↥L) * Nat.card ↥(C ⊓ L) := by rw [← h2]
      _ = Nat.card ↥(C ⊓ L) * Nat.card ↥(B ⊓ (L ⊔ C)) * Nat.card ↥L := by ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmain

end CFSG.StandardType.E6QTwo

end
