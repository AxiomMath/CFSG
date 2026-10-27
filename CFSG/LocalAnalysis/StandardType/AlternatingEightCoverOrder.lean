module

public import CFSG.LocalAnalysis.StandardType.AlternatingEightCoverElements

public section

namespace CFSG.StandardType

variable {J : Type*} [Group J] [Finite J]

theorem card_alternatingGroup_fin_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem IsAlternatingEightCover.card_eq (hJ : IsAlternatingEightCover J) :
    Nat.card J = 20160 * Nat.card (Subgroup.center J) := by
  obtain ⟨-, ⟨e⟩, -⟩ := hJ
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_eight] at h
  rw [h, mul_comm]

theorem IsAlternatingEightCover.nontrivial (hJ : IsAlternatingEightCover J) : Nontrivial J := by
  rw [← Finite.one_lt_card_iff_nontrivial, IsAlternatingEightCover.card_eq hJ]
  haveI : Nonempty (Subgroup.center J) := ⟨1, Subgroup.one_mem _⟩
  have hpos : 0 < Nat.card (Subgroup.center J) := Nat.card_pos
  nlinarith

theorem IsAlternatingEightCover.not_dvd_card_twentySeven (hJ : IsAlternatingEightCover J) :
    ¬ 27 ∣ Nat.card J := by
  intro h27
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hJ.2.2
  rw [IsAlternatingEightCover.card_eq hJ, hk] at h27
  have hcop : Nat.Coprime 27 (2 ^ k) := (by norm_num : Nat.Coprime 27 2).pow_right k
  have hdvd : 27 ∣ 20160 := hcop.dvd_of_dvd_mul_right h27
  norm_num at hdvd

end CFSG.StandardType
