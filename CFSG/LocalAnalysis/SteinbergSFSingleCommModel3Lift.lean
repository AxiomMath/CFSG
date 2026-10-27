module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

theorem model3_exists_sylow_lift {X Y : Type*} [Group X] [Group Y] [Finite X] (γ : X →* Y)
    (hγ : Function.Surjective γ) (hodd : Odd (Nat.card γ.ker)) {V : Subgroup Y}
    (hV : ∃ R : Sylow 2 Y, (R : Subgroup Y) = V) :
    ∃ W : Sylow 2 X, (W : Subgroup X).map γ = V ∧ (W : Subgroup X) ⊓ γ.ker = ⊥ := by
  obtain ⟨R, hR⟩ := hV
  obtain ⟨W, hW⟩ := Sylow.mapSurjective_surjective hγ 2 R
  refine ⟨W, ?_, ?_⟩
  · rw [← hR, ← hW]
    exact (Sylow.coe_mapSurjective hγ W).symm
  ·
    have hWK : IsPGroup 2 ↥((W : Subgroup X) ⊓ γ.ker) :=
      W.isPGroup'.to_le inf_le_left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hWK
    have hcard : Nat.card ↥((W : Subgroup X) ⊓ γ.ker) = 1 := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [hn, h0, pow_zero]
      · exfalso
        have h2 : 2 ∣ Nat.card ↥((W : Subgroup X) ⊓ γ.ker) := by
          rw [hn]
          exact dvd_pow_self 2 hpos.ne'
        exact hodd.not_two_dvd_nat (h2.trans (Subgroup.card_dvd_of_le inf_le_right))
    exact Subgroup.card_eq_one.mp hcard

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
