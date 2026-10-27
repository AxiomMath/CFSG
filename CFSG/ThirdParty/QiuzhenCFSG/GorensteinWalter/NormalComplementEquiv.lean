module

public import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Transporting normal complements across group equivalences
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

/-- Complementary subgroups remain complementary under a group
equivalence. -/
public theorem isComplement_map_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (A B : Subgroup G) (e : G ≃* H) (h : A.IsComplement' B) :
    (A.map e.toMonoidHom).IsComplement' (B.map e.toMonoidHom) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective e.injective, h.card_mul,
      Nat.card_congr e.toEquiv]
  · rw [disjoint_iff]
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨hzA, hzB⟩
      rcases Subgroup.mem_map.mp hzA with ⟨a, ha, hfa⟩
      rcases Subgroup.mem_map.mp hzB with ⟨b, hb, hfb⟩
      have hab : a = b := e.injective (hfa.trans hfb.symm)
      have haone : a = 1 :=
        Subgroup.mem_bot.mp (h.disjoint.le_bot ⟨ha, hab ▸ hb⟩)
      exact Subgroup.mem_bot.mpr (by rw [← hfa, haone]; simp)
    · exact bot_le

/-- A normal complement of a normalizer transports across a group
equivalence. -/
public theorem normalComplement_map_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (P Q : Subgroup G) (e : G ≃* H)
    (hQnormal : Q.Normal)
    (hcomp : Q.IsComplement' (Subgroup.normalizer (P : Set G))) :
    (Q.map e.toMonoidHom).Normal ∧
      (Q.map e.toMonoidHom).IsComplement'
        (Subgroup.normalizer ((P.map e.toMonoidHom) : Set H)) := by
  have hmap := isComplement_map_mulEquiv Q
    (Subgroup.normalizer (P : Set G)) e hcomp
  constructor
  · exact hQnormal.map e.toMonoidHom e.surjective
  · rw [← Subgroup.map_equiv_normalizer_eq P e]
    exact hmap

end CFSG.GorensteinWalter
