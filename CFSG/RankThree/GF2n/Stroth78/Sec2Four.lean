module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld (Qa)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem map_R0_eq_Rbar (S : Setting z E F) (a : G) :
    Subgroup.map (QuotientGroup.mk' ((Q z).subgroupOf (H z)))
        ((centerIn (QaOf a) ⊓ H z).subgroupOf (H z)) = Rbar S a := by
  have hQmap : Subgroup.map (QuotientGroup.mk' ((Q z).subgroupOf (H z)))
      ((Q z).subgroupOf (H z)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Rbar, Ra, Subgroup.subgroupOf_sup (Q_le_H S) inf_le_right, Subgroup.map_sup, hQmap,
    bot_sup_eq]

theorem card_Rbar_mul (S : Setting z E F) (a : G) :
    Nat.card (Rbar S a) * Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) =
      Nat.card (centerIn (QaOf a) ⊓ H z : Subgroup G) := by
  let f : ↥(centerIn (QaOf a) ⊓ H z) →* Hbar z :=
    (QuotientGroup.mk' ((Q z).subgroupOf (H z))).comp
      (Subgroup.inclusion (inf_le_right : centerIn (QaOf a) ⊓ H z ≤ H z))
  have hrange : f.range = Rbar S a := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, map_R0_eq_Rbar]
  have hker : f.ker = (Q z).subgroupOf (centerIn (QaOf a) ⊓ H z) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (QuotientGroup.mk (Subgroup.inclusion
      (inf_le_right : centerIn (QaOf a) ⊓ H z ≤ H z) x) : Hbar z) = 1 ↔
      x ∈ (Q z).subgroupOf (centerIn (QaOf a) ⊓ H z)
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hinf : Q z ⊓ (centerIn (QaOf a) ⊓ H z) = centerIn (QaOf a) ⊓ Q z := by
    rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left (Q_le_H S)), inf_comm]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker, ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Q z ⊓ (centerIn (QaOf a) ⊓ H z) ≤ centerIn (QaOf a) ⊓ H z)).toEquiv,
    hinf, mul_comm] at h
  exact h

end CFSG.RankThree.GF2n.Stroth78
