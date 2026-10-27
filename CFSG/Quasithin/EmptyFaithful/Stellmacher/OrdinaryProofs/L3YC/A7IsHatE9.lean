module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6Centre
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7IsHatE9

theorem isHat_seven_E9_meets_centre {X : Type} [Group X] [Finite X]
    (hX : CFSG.Quasithin.IsHat X (alternatingGroup (Fin 7)))
    (E : Subgroup X) (hE : Nat.card E = 9) : E ⊓ Subgroup.center X ≠ ⊥ := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := hX
  obtain ⟨hperf, -⟩ := hq
  have : Group.IsPerfect X := hperf
  have hidx : (Subgroup.center X).index = 2520 := by
    have h := Nat.card_congr f.toEquiv
    rw [card_alternatingGroup_seven] at h
    exact h
  have hG : Nat.card X = 27 * 280 := by
    have h := Subgroup.card_mul_index (Subgroup.center X)
    rw [hc, hidx] at h
    omega
  have hm : Nat.Coprime 280 3 := by norm_num
  rw [inf_comm]
  exact inf_ne_bot_of_perfect (N := Subgroup.center X) (E := E) le_rfl hc 280 hG hm hE

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7IsHatE9

end
