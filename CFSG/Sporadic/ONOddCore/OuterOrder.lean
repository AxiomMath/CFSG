module

public import CFSG.Sporadic.ONOddCore.OuterEmbeds
public import CFSG.Sporadic.ONOddCore.LocalAutOrders

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ComponentClassification.OuterAutomorphisms

theorem card_dvd_four_of_embeds
    {G : Type*} [Group G] {f : G →* Outer onM}
    (hf : Function.Injective f) : Nat.card G ∣ 4 := by
  rw [← card_outer_M, ← Nat.card_range_of_injective hf]
  exact Subgroup.card_subgroup_dvd_card f.range

theorem r3e_on_outer_order_divides_four :
    Nat.card (Outer Blueprint.NativeSporadic.ON) ∣ 4 ∧
      (Nat.card (Outer Blueprint.NativeSporadic.ON) = 1 ∨
        Nat.card (Outer Blueprint.NativeSporadic.ON) = 2 ∨
          Nat.card (Outer Blueprint.NativeSporadic.ON) = 4) := by
  obtain ⟨f, hf⟩ := r3e_on_outer_action_embeds_in_local_outer_group.2
  have h := card_dvd_four_of_embeds hf
  refine ⟨h, ?_⟩
  have hle := Nat.le_of_dvd (by norm_num) h
  generalize Nat.card (Outer Blueprint.NativeSporadic.ON) = c at h hle ⊢
  interval_cases c <;> revert h <;> decide

end CFSG.Sporadic.ONOddCore
