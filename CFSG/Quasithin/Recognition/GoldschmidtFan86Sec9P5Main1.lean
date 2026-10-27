module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Star
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg1c

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_9_10b {F : FanTree Γ G} {L : ZLab Γ G} (H : P5Hyp F L) : Fan910b F L :=
  fun S hS => (H.h98 S).1 (S.star_sq H hS)

theorem fan_9_12 {F : FanTree Γ G} {L : ZLab Γ G} (H : P5Hyp F L) : Fan912 F L := by
  intro S hS
  obtain ⟨e₁, e₂, hw2⟩ := fan_9_10b H S hS
  have hids := S.ids H hS (e₁ := (e₁ : ℕ)) (e₂ := (e₂ : ℕ)) (by omega) (by omega) hw2
  have hR := S.p1Rel H
  refine ⟨hids.p2Rel912 hR, fun h4 => ?_, fun h2 => ?_⟩
  · exact hids.p2cRel912 hR (S.p1cRel H h4) (S.fcomm_wc H h4)
  ·
    obtain ⟨-, -, -, a4, -, -, -, -, -, -⟩ := H.h95.2.2.2 S
    have hz : L.z S.α ∈ Subgroup.zpowers S.c := by
      rw [← S.gen]
      exact S.D.z_mem_calpha F H.h7.2.2.1 H.h512
    have hord : orderOf S.c = 2 := by
      rw [← Nat.card_zpowers, ← S.gen]
      exact h2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hk2 : S.c ^ (k % 2) = L.z S.α := by
      rw [← hk]
      have := zpow_mod_orderOf S.c k
      rw [hord] at this
      exact_mod_cast this
    rw [a4]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk2
      exact absurd hk2.symm (L.z_ne_one S.D.val)
    · rw [h1, zpow_one] at hk2
      exact hk2

end CFSG.Quasithin.Fan86
