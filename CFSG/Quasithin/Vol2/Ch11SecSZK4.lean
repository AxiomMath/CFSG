module

public import CFSG.Quasithin.Vol2.Ch11SecSX1
public import CFSG.Quasithin.Vol2.Ch11SecSZK2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

omit [Finite Q] in
theorem L34Data.card_sup_eq (hD : L34Data B) {O : Subgroup Q}
    (hBO : B ≤ Subgroup.normalizer (O : Set Q)) (hO : Odd (Nat.card ↥O)) :
    Nat.card ↥(B ⊔ O) = Nat.card ↥B * Nat.card ↥O := by
  have hN : (O.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    exact fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hBO hb, Subgroup.le_normalizer hb⟩
  have hc : Nat.card ↥(O.subgroupOf B) = Nat.card ↥(O ⊓ B) := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hodd : Odd (Nat.card ↥(O.subgroupOf B)) := by
    rw [hc]
    exact hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hbot := hD.odd _ hN hodd
  have hOB : O ⊓ B = ⊥ := by
    rw [← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
  have h2 := Subgroup.relIndex_mul_card O B
  rw [hOB, Subgroup.card_bot, mul_one] at h2
  have h3 := Subgroup.relIndex_mul_card O (B ⊔ O)
  rw [relIndex_sup_eq' hBO, h2, inf_eq_left.mpr le_sup_right] at h3
  exact h3.symm

theorem L34Data.false_of_nonquasi (hD : L34Data B) (hBL : B ≤ L) (h : A312Nonquasi B L) :
    False := by
  have hOLL : (CFSG.oddCore ↥L).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hLO :
      L ≤ Subgroup.normalizer (((CFSG.oddCore ↥L).map L.subtype : Subgroup Q) : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOLL).mp ?_
    have he : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [he]
    infer_instance
  have hOcard : Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) = Nat.card ↥(CFSG.oddCore ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hOodd : Odd (Nat.card ↥((CFSG.oddCore ↥L).map L.subtype)) := by
    rw [hOcard]
    exact A37.odd_card_oddCore _
  have h1 := hD.card_sup_eq (hBL.trans hLO) hOodd
  have hpos : 0 < Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := Nat.card_pos
  have hle := hD.le_card
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, hNeq, hN5⟩
  · rw [← hLB] at h1
    have h2 := (CFSG.oddCore ↥L).card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 hp hSL, ← hOcard] at h2
    have hB : Nat.card ↥B = p * (p ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    refine hD.false_of_prime_dvd_card hp hp2 (hB ▸ dvd_mul_right p _) fun hp' => ?_
    rcases hp' with rfl | rfl | rfl <;> omega
  · have h2 := N.card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 (by norm_num) hN5] at h2
    have h3 : Nat.card ↥N = Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := by
      rw [hNeq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h3] at h2
    have hB : Nat.card ↥B = 5 * (5 ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    omega

end CFSG.Quasithin.Vol2.Ch11.SecS
