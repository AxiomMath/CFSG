module

public import CFSG.OddTranspositions.HypothesisC
public import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem meetsSq_of_card_closure_alpha (hC : HypothesisC D)
    (hcomm : ∀ a ∈ hC.alpha, ∀ b ∈ hC.alpha, Commute a b)
    (hcard : Nat.card (Subgroup.closure hC.alpha) ≤ hC.alpha.ncard + 1)
    (h2 : 2 ≤ hC.alpha.ncard) : MeetsSq D := by
  have hαD : hC.alpha ⊆ D := hC.isBlock_alpha.subset
  have h1 : (1 : G) ∉ hC.alpha := fun h => hC.setup.oddT.ne_one (hαD h) rfl
  have heq : insert (1 : G) hC.alpha = (Subgroup.closure hC.alpha : Set G) := by
    refine Set.eq_of_subset_of_ncard_le
      (Set.insert_subset (Subgroup.one_mem _) Subgroup.subset_closure) ?_ (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem h1 (Set.toFinite _), ← Nat.card_coe_set_eq]
    exact hcard
  obtain ⟨a, b, ha, hb, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
  have hab : a * b ∈ insert (1 : G) hC.alpha := heq ▸
    Subgroup.mul_mem _ (Subgroup.subset_closure ha) (Subgroup.subset_closure hb)
  rcases hab with h | h
  · exact absurd ((eq_inv_of_mul_eq_one_right h).trans
      (inv_eq_of_mul_eq_one_right (hC.setup.oddT.mul_self_eq_one (hαD ha)))).symm hne
  · exact ⟨a, hαD ha, b, hαD hb, hne, hcomm a ha b hb, hαD h⟩

end CFSG.OddTranspositions.PartFour
