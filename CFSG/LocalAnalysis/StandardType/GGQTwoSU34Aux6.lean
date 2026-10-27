module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux5
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Bruhat

public section

open scoped Pointwise

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qTwoS34_card_coordBlockSU {N : ℕ} (J : Finset (Fin N)) :
    Nat.card ↥(coordBlockSU K 2 1 J) = Nat.card (Su K 2 1 J.card) := by
  have e : Su K 2 1 J.card ≃ ↥(coordBlockSU K 2 1 J) :=
    Equiv.ofInjective (blockSUOn K 2 1 J) (blockSUOn_injective J)
  exact (Nat.card_congr e).symm

theorem qTwoS34_card_coordBlockSU_three (hK : Nat.card K = 4) {N : ℕ} {J : Finset (Fin N)}
    (hJ : J.card = 3) : Nat.card ↥(coordBlockSU K 2 1 J) = 216 := by
  rw [qTwoS34_card_coordBlockSU, hJ, qTwoS34_card_Su_three hK]

theorem qTwoS34_card_inf (hK : Nat.card K = 4) {N : ℕ} {A B : Finset (Fin N)}
    (hA : A.card = 3) (hB : B.card = 3) (hAB : (A ∪ B).card = 4) :
    Nat.card ↥(coordBlockSU K 2 1 A ⊓ coordBlockSU K 2 1 B) = 6 := by
  rw [qTwoS34_coordBlockSU_inf, qTwoS34_card_coordBlockSU]
  have hcard : (A ∩ B).card = 2 := by
    have := Finset.card_union_add_card_inter A B
    omega
  rw [hcard, qTwoS34_card_Su_two hK]

theorem qTwoS34_card_mul_set (hK : Nat.card K = 4) {N : ℕ} {A B : Finset (Fin N)}
    (hA : A.card = 3) (hB : B.card = 3) (hAB : (A ∪ B).card = 4) :
    (((coordBlockSU K 2 1 A : Set (Su K 2 1 N)) *
      (coordBlockSU K 2 1 B : Set (Su K 2 1 N))).ncard) = 7776 := by
  have hA216 := qTwoS34_card_coordBlockSU_three hK hA
  have hB216 := qTwoS34_card_coordBlockSU_three hK hB
  have hI6 := qTwoS34_card_inf hK hA hB hAB
  have hmul := CFSG.LocalAnalysis.EvenBN.TrialityD4.ncard_mul_mul_card_inf
    (coordBlockSU K 2 1 A) (coordBlockSU K 2 1 B)
  rw [hA216, hB216, hI6] at hmul
  have h7776 : 216 * 216 = 7776 * 6 := by norm_num
  rw [h7776] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) hmul

theorem qTwoS34_card_sup_ge (hK : Nat.card K = 4) {N : ℕ} {A B : Finset (Fin N)}
    (hA : A.card = 3) (hB : B.card = 3) (hAB : (A ∪ B).card = 4) :
    7776 ≤ Nat.card ↥(coordBlockSU K 2 1 A ⊔ coordBlockSU K 2 1 B) := by
  have hset := qTwoS34_card_mul_set hK hA hB hAB
  have hsub : ((coordBlockSU K 2 1 A : Set (Su K 2 1 N)) *
      (coordBlockSU K 2 1 B : Set (Su K 2 1 N))) ⊆
      ((coordBlockSU K 2 1 A ⊔ coordBlockSU K 2 1 B : Subgroup (Su K 2 1 N)) :
        Set (Su K 2 1 N)) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hle := Set.ncard_le_ncard hsub
  rw [hset] at hle
  have hcoe : Set.ncard ((coordBlockSU K 2 1 A ⊔ coordBlockSU K 2 1 B : Subgroup (Su K 2 1 N)) :
      Set (Su K 2 1 N)) = Nat.card ↥(coordBlockSU K 2 1 A ⊔ coordBlockSU K 2 1 B) := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  rw [hcoe] at hle
  exact hle

theorem qTwoS34_card_Su_four (hK : Nat.card K = 4) : Nat.card (Su K 2 1 4) = 25920 :=
  card_Su_four hK

end CFSG.StandardType.QTwo

end
